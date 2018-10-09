> module Data.List.Any.Properties where

LICENSE, from the Agda standard library version 0.13
Homepage of Agda standard library:
http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary



Copyright (c) 2007-2016 Nils Anders Danielsson, Ulf Norell, Shin-Cheng
Mu, Samuel Bronson, Dan Doel, Patrik Jansson, Liang-Ting Chen,
Jean-Philippe Bernardy, Andrés Sicard-Ramírez, Nicolas Pouillard,
Darin Morrison, Peter Berry, Daniel Brown, Simon Foster, Dominique
Devriese, Andreas Abel, Alcatel-Lucent, Eric Mertens, Joachim
Breitner, Liyang Hu, Noam Zeilberger, Érdi Gergő, Stevan Andjelkovic,
Helmut Grohne, Guilhem Moulin, Noriyuki OHKAWA, Evgeny Kotelnikov,
James Chapman, Pepijn Kokke and some anonymous contributors.

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


Copied code from the standard library:

\begin{code}
open import Data.List            using (List ; [] ; _∷_ ; _++_)
open import Data.List.Any        using (Any ; any ; here ; there)
open import Data.Sum as Sum      using (_⊎_ ; inj₁ ; inj₂)
open import Function             using (id)

++⁺ˡ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
       Any P xs → Any P (xs ++ ys)
++⁺ˡ (here p)  = here p
++⁺ˡ (there p) = there (++⁺ˡ p)

++⁺ʳ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} →
       Any P ys → Any P (xs ++ ys)
++⁺ʳ []       p = p
++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} →
      Any P (xs ++ ys) → Any P xs ⊎ Any P ys
++⁻ []       p         = inj₂ p
++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

{- the definition of ++-comm copied from Data.List.Any.Properties
   because I could not figure out how to reuse the definition
   that is in there (also inlined ∘ since I didn't find its
   definition) -}
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
++-comm : ∀ {a p} {A : Set a} {P : A → Set p} xs ys →
            Any P (xs ++ ys) → Any P (ys ++ xs)
++-comm xs ys thing =  ([ ++⁺ʳ ys , ++⁺ˡ ]′ (++⁻ xs thing))


-- ++ˡ = ++⁺ˡ
-- ++ʳ = ++⁺ʳ
\end{code}

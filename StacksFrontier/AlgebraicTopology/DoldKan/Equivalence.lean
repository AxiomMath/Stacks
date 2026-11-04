module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The Dold–Kan equivalence for abelian categories

The Dold–Kan equivalence between simplicial objects and connective chain complexes in an abelian
category, together with the criterion for an equivalence of abelian categories used to deduce it.
-/

/-!
## Dold-Kan

Let `A` be an abelian category. The normalized complex functor `N : Simp(A) ⥤ Ch_{≥0}(A)` sends a
simplicial object `U` of `A` to the chain complex with `N(U)_0 = U_0`, `N(U)_m = ⋂_i Ker(d^m_i)`
(the intersection of the kernels of all face maps in degree `m` but one) and differential induced
by the remaining face map; this is Mathlib's `AlgebraicTopology.normalizedMooreComplex A`. It is
faithful: a morphism of simplicial objects is determined by its restriction to the normalized
subobjects, because those subobjects split `U`. Being faithful between abelian categories, `N` is
moreover conservative: it reflects monomorphisms, epimorphisms and isomorphisms.

### Main results

* `AlgebraicTopology.normalizedMooreComplex_faithful`: the normalized complex functor
  `N : Simp(A) ⥤ Ch_{≥0}(A)` of an abelian category is faithful, hence reflects monomorphisms,
  epimorphisms and isomorphisms.

### References

* [Stacks, Tag 019E](https://stacks.math.columbia.edu/tag/019E)
-/

section

open CategoryTheory

universe v u

namespace AlgebraicTopology

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- **Stacks 019E**.
The normalized complex functor `N : Simp(A) ⥤ Ch_{≥0}(A)` of an abelian category `A`, sending a
simplicial object `U` to the complex of normalized chains `N(U)_m = ⋂_i Ker(d^m_i)`, is faithful.
Consequently it reflects monomorphisms, epimorphisms and isomorphisms. -/
@[stacks 019E]
public instance normalizedMooreComplex_faithful :
    (normalizedMooreComplex A).Faithful :=
  Functor.Faithful.of_iso (eqToIso (Abelian.DoldKan.equivalence_functor (A := A)))

end AlgebraicTopology

end

/-!
## A criterion for an equivalence of abelian categories

Let `A` and `B` be abelian categories and let `N : A ⥤ B` and `S : B ⥤ A` be exact functors with a
natural isomorphism `g : S ⋙ N ≅ 𝟭 B`. If `N` is faithful and `S` is essentially surjective, then
`S` and `N` are quasi-inverse equivalences of categories: there is a natural isomorphism
`N ⋙ S ≅ 𝟭 A`, and `N` and `S` are the functor and the inverse functor of an equivalence `A ≌ B`.

The exactness of `N` and `S` is not needed for the conclusion, so it is not assumed below.

### Main definitions

* `CategoryTheory.Functor.compIsoIdOfFaithfulOfEssSurj`: the natural isomorphism `N ⋙ S ≅ 𝟭 A`.

### Main results

* `CategoryTheory.Functor.nonempty_compIsoId_of_faithful_of_essSurj`: under the hypotheses above
  there is a natural isomorphism `N ⋙ S ≅ 𝟭 A`.
* `CategoryTheory.Equivalence.exists_of_faithful_of_essSurj`: under the hypotheses above `N` and
  `S` are the functor and the inverse functor of an equivalence of categories `A ≌ B`.

### References

* [Stacks, Tag 019F](https://stacks.math.columbia.edu/tag/019F)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The natural isomorphism `N ⋙ S ≅ 𝟭 A` attached to a natural isomorphism `g : S ⋙ N ≅ 𝟭 B`
with `N` faithful and `S` essentially surjective. -/
noncomputable def Functor.compIsoIdOfFaithfulOfEssSurj
    {A B : Type*} [Category A] [Category B]
    (N : A ⥤ B) (S : B ⥤ A)
    (g : S ⋙ N ≅ 𝟭 B)
    (hN_faithful : N.Faithful)
    (hS_essSurj : S.EssSurj) :
    N ⋙ S ≅ 𝟭 A := by
  have : N.Faithful := hN_faithful
  have : S.EssSurj := hS_essSurj
  have : S.Faithful := Functor.Faithful.of_comp_iso g
  have : S.Full := Functor.Full.of_comp_faithful_iso g
  have : S.IsEquivalence := { }
  let E : B ≌ A := S.asEquivalence
  have hE : S ≅ E.functor := eqToIso S.asEquivalence_functor.symm
  have NisoInv : N ≅ E.inverse :=
    (Functor.leftUnitor N).symm ≪≫
      Functor.isoWhiskerRight E.counitIso.symm N ≪≫
      Functor.associator E.inverse E.functor N ≪≫
      Functor.isoWhiskerLeft E.inverse (Functor.isoWhiskerRight hE.symm N ≪≫ g) ≪≫
      Functor.rightUnitor E.inverse
  exact Functor.isoWhiskerLeft N hE ≪≫ Functor.isoWhiskerRight NisoInv E.functor ≪≫ E.counitIso

/-- For abelian categories `A` and `B` and functors `N : A ⥤ B`, `S : B ⥤ A` with a natural
isomorphism `g : S ⋙ N ≅ 𝟭 B`, `N` faithful and `S` essentially surjective, there is a natural
isomorphism `N ⋙ S ≅ 𝟭 A`. -/
theorem Functor.nonempty_compIsoId_of_faithful_of_essSurj
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (N : A ⥤ B) (S : B ⥤ A)
    (g : S ⋙ N ≅ 𝟭 B)
    (hN_faithful : N.Faithful)
    (hS_essSurj : S.EssSurj) :
    Nonempty (N ⋙ S ≅ 𝟭 A) :=
  ⟨Functor.compIsoIdOfFaithfulOfEssSurj N S g hN_faithful hS_essSurj⟩

/-- **Stacks 019F**.
For abelian categories `A` and `B` and exact functors `N : A ⥤ B`, `S : B ⥤ A` with a natural
isomorphism `g : S ⋙ N ≅ 𝟭 B`, `N` faithful and `S` essentially surjective, `N` and `S` are
quasi-inverse equivalences of categories: there is an equivalence `A ≌ B` whose functor is `N` and
whose inverse functor is `S`. -/
@[stacks 019F]
theorem Equivalence.exists_of_faithful_of_essSurj
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (N : A ⥤ B) (S : B ⥤ A)
    (g : S ⋙ N ≅ 𝟭 B)
    (hN_faithful : N.Faithful)
    (hS_essSurj : S.EssSurj) :
    ∃ e : A ≌ B, e.functor = N ∧ e.inverse = S :=
  ⟨Equivalence.mk N S
    (Functor.compIsoIdOfFaithfulOfEssSurj N S g hN_faithful hS_essSurj).symm g, rfl, rfl⟩

end CategoryTheory

end

end

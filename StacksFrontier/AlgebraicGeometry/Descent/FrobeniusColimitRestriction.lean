module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.OverPullbackLimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# The colimit along an endomorphism commutes with restriction to an open

Let `φ : R ⟶ R` be an endomorphism of an object of a category and let `T` be a functor preserving
the colimit of the sequential diagram `R → R → R → ⋯` of iterates of `φ`. Then `T` carries that
colimit to the colimit of the iterates of `T.map φ`:

`T (colim φ) ≅ colim (T.map φ)`.

Specialising `T` to the restriction of sheaves of rings to a slice site — which preserves colimits
because it is a left adjoint — gives **`colim_F 𝒪_X` restricted to an open `U` is the colimit along
the restricted Frobenius**, the compatibility of the sheaf of rings of Stacks Tag 0EXB with passing
to an open.

## Main definitions

* `CategoryTheory.Limits.endoSequenceComp` and `CategoryTheory.Limits.endoSequenceCompIso`: the
  image under `T` of the diagram of iterates of `φ` is the diagram of iterates of `T.map φ`.
* `CategoryTheory.Limits.endoColimitCompIso`: the comparison `T (colim φ) ≅ colim (T.map φ)`.
* `CategoryTheory.Limits.ringSheafEndoColimitOverIso`: that comparison for the restriction of
  sheaves of rings to a slice site.
* `AlgebraicGeometry.frobeniusColimitRingSheafOverIso`: **`colim_F 𝒪_X` commutes with restriction
  to an open.**

## Main results

* `CategoryTheory.Limits.map_endoColimitι_comp_endoColimitCompIso_hom`: the comparison carries the
  image of the stage-`n` coprojection to the stage-`n` coprojection. This characterises it, by
  `CategoryTheory.Limits.endoColimit_hom_ext`.
* `CategoryTheory.Limits.endoColimitCompIso_hom_comp_endoColimitMap`: the comparison is compatible
  with the endomorphisms the two colimits carry. At Frobenius this says the identification of
  `(colim_F 𝒪_X)|_U` with `colim_F (𝒪_X|_U)` respects the Frobenius action, which is what makes it
  an identification of the objects Stacks Tag 0EXB is about and not merely of sheaves of rings.
* `CategoryTheory.Limits.overPullback_map_hom_app` and
  `AlgebraicGeometry.overPullback_frobeniusRingSheafOnOpensHom_app`: restriction to a slice site
  acts on sections by the original morphism, so the endomorphism appearing on the right of
  `AlgebraicGeometry.frobeniusColimitRingSheafOverIso` is again the `p`-th power map.

## Implementation notes

**The endomorphism is a variable.** Everything is proved for an arbitrary endomorphism of an
arbitrary object and an arbitrary colimit-preserving functor, and Frobenius enters only in the last
two declarations. Stated concretely at `AlgebraicGeometry.frobeniusRingCatSheafHom`, the same
identifications ask the elaborator to unfold the sequential colimit of the structure sheaf; with
the morphism as a variable nothing of the colimit is ever unfolded and the proofs are the
universal property.

**Why `CategoryTheory.NatTrans.ofSequence` and not `CategoryTheory.NatIso.ofComponents`.** The two
diagrams `endoSequence φ ⋙ T` and `endoSequence (T.map φ)` have the same value `T.obj R` at every
stage, so the comparison is the identity in every component; but
`CategoryTheory.NatIso.ofComponents` asks for naturality against *every* morphism of `ℕ`, and
`CategoryTheory.Functor.ofSequence` — out of which `endoSequence` is built — records only the
single steps `n ⟶ n + 1`.
`CategoryTheory.NatTrans.ofSequence` asks for naturality across a single step only, which is where
`CategoryTheory.Limits.endoSequence_map_succ` applies, and invertibility is then checked
componentwise.

**Where the colimit preservation comes from.** Restriction of sheaves to a slice site is the left
adjoint of `CategoryTheory.Functor.sheafPushforwardCocontinuous` whenever the pointwise right Kan
extensions along `(Over.forget V).op` exist; that is
`CategoryTheory.GrothendieckTopology.preservesColimits_overPullback`, which is used rather than
reproved. For `RingCat.{u}` on a site whose objects and morphisms lie in `Type u` those Kan
extensions exist because `RingCat.{u}` has all `u`-small limits, so the hypothesis is discharged by
instance search and `CategoryTheory.Limits.ringSheafEndoColimitOverIso` carries none.

**Universes of the shape.** `ℕ` is a category in `Type 0` with morphisms in `Type 0`, so what the
colimit of a sequential diagram needs is `PreservesColimitsOfSize.{0, 0}`, which is the instance
of `CategoryTheory.GrothendieckTopology.preservesColimits_overPullback` at those two universes.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius

universe v u v' u'

namespace CategoryTheory.Limits

section Comp

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟] {R : 𝒞}

/-- The comparison from the image under `T` of the diagram of iterates of `φ` to the diagram of
iterates of `T.map φ`. Every component is an identity. -/
noncomputable def endoSequenceComp (φ : R ⟶ R) (T : 𝒞 ⥤ 𝒟) :
    endoSequence φ ⋙ T ⟶ endoSequence (T.map φ) :=
  NatTrans.ofSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
    simp only [Functor.comp_map, endoSequence_map_succ]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Every component of `endoSequenceComp φ T` is the identity of `T.obj R`. -/
@[simp]
lemma endoSequenceComp_app (φ : R ⟶ R) (T : 𝒞 ⥤ 𝒟) (n : ℕ) :
    (endoSequenceComp φ T).app n = 𝟙 (T.obj R) :=
  NatTrans.ofSequence_app _ _ n

/-- Every component of `endoSequenceComp φ T` is an isomorphism. -/
instance isIso_endoSequenceComp_app (φ : R ⟶ R) (T : 𝒞 ⥤ 𝒟) (n : ℕ) :
    IsIso ((endoSequenceComp φ T).app n) :=
  inferInstanceAs (IsIso (𝟙 (T.obj R)))

/-- **The image of the diagram of iterates of an endomorphism is the diagram of iterates of its
image.** -/
noncomputable def endoSequenceCompIso (φ : R ⟶ R) (T : 𝒞 ⥤ 𝒟) :
    endoSequence φ ⋙ T ≅ endoSequence (T.map φ) :=
  haveI : IsIso (endoSequenceComp φ T) := NatIso.isIso_of_isIso_app _
  asIso (endoSequenceComp φ T)

variable (φ : R ⟶ R) (T : 𝒞 ⥤ 𝒟) [HasColimit (endoSequence φ)]
  [HasColimit (endoSequence (T.map φ))] [PreservesColimit (endoSequence φ) T]

/-- **A functor preserving the colimit of the iterates of an endomorphism carries it to the colimit
of the iterates of the image endomorphism.** -/
noncomputable def endoColimitCompIso :
    T.obj (colimit (endoSequence φ)) ≅ colimit (endoSequence (T.map φ)) :=
  (isColimitOfPreserves T (colimit.isColimit (endoSequence φ))).coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv (endoSequenceCompIso φ T)
      (colimit.cocone (endoSequence (T.map φ)))).symm (colimit.isColimit _))

/-- **The comparison carries the image of the stage-`n` coprojection to the stage-`n`
coprojection.** With `CategoryTheory.Limits.endoColimit_hom_ext` this characterises it. -/
@[simp]
lemma map_endoColimitι_comp_endoColimitCompIso_hom (n : ℕ) :
    T.map (endoColimitι φ n) ≫ (endoColimitCompIso φ T).hom = endoColimitι (T.map φ) n := by
  have h := (isColimitOfPreserves T
    (colimit.isColimit (endoSequence φ))).comp_coconePointUniqueUpToIso_hom
      ((IsColimit.precomposeHomEquiv (endoSequenceCompIso φ T)
        (colimit.cocone (endoSequence (T.map φ)))).symm (colimit.isColimit _)) n
  refine h.trans ?_
  change (endoSequenceCompIso φ T).hom.app n ≫ endoColimitι (T.map φ) n = _
  rw [show (endoSequenceCompIso φ T).hom.app n = 𝟙 (T.obj R) from endoSequenceComp_app φ T n]
  exact Category.id_comp _

/-- **The comparison is compatible with the endomorphisms induced on the two colimits.** -/
lemma endoColimitCompIso_hom_comp_endoColimitMap :
    T.map (endoColimitMap φ) ≫ (endoColimitCompIso φ T).hom =
      (endoColimitCompIso φ T).hom ≫ endoColimitMap (T.map φ) := by
  refine (isColimitOfPreserves T (colimit.isColimit (endoSequence φ))).hom_ext fun n ↦ ?_
  change T.map (endoColimitι φ n) ≫ T.map (endoColimitMap φ) ≫ _ =
    T.map (endoColimitι φ n) ≫ _ ≫ _
  rw [← Category.assoc, ← T.map_comp, endoColimitι_comp_endoColimitMap, T.map_comp,
    Category.assoc, map_endoColimitι_comp_endoColimitCompIso_hom, ← Category.assoc,
    map_endoColimitι_comp_endoColimitCompIso_hom, endoColimitι_comp_endoColimitMap]

end Comp

section OverPullback

variable {C : Type u} [Category.{u} C]

/-- Restriction of a morphism of sheaves to a slice site acts on the sections over an object of the
slice by the action of the original morphism on the sections over its underlying object. -/
lemma overPullback_map_hom_app {A : Type u'} [Category.{v'} A] (J : GrothendieckTopology C)
    (U : C) {F G : Sheaf J A} (α : F ⟶ G) (V : (Over U)ᵒᵖ) :
    ((J.overPullback A U).map α).hom.app V = α.hom.app (Opposite.op V.unop.left) := rfl

variable {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}

/-- **The colimit of a sheaf of rings along an endomorphism commutes with restriction to a slice
site.** -/
noncomputable def ringSheafEndoColimitOverIso (ψ : S ⟶ S) (U : C) :
    (ringSheafEndoColimit ψ).over U ≅
      ringSheafEndoColimit ((J.overPullback RingCat.{u} U).map ψ) :=
  letI : PreservesColimitsOfSize.{0, 0} (J.overPullback RingCat.{u} U) :=
    GrothendieckTopology.preservesColimits_overPullback.{0, 0} J RingCat.{u} U
  endoColimitCompIso ψ (J.overPullback RingCat.{u} U)

end OverPullback

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **`colim_F 𝒪_X` commutes with restriction to an open.** The restriction to `U` of the colimit
of the structure sheaf along Frobenius is the colimit along the restriction of Frobenius, which by
`AlgebraicGeometry.overPullback_frobeniusRingSheafOnOpensHom_app` is again the `p`-th power map on
sections. -/
noncomputable def frobeniusColimitRingSheafOverIso (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : Opens (X : TopCat)) :
    (frobeniusColimitRingSheaf X p hX).over U ≅
      ringSheafEndoColimit
        (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} U).map
          (frobeniusRingSheafOnOpensHom X p hX)) :=
  ringSheafEndoColimitOverIso (frobeniusRingSheafOnOpensHom X p hX) U

/-- **The restriction to an open of the Frobenius endomorphism of `𝒪_X` is again the `p`-th power
map on sections**, so the endomorphism whose colimit the right-hand side of
`AlgebraicGeometry.frobeniusColimitRingSheafOverIso` takes is Frobenius again. -/
lemma overPullback_frobeniusRingSheafOnOpensHom_app (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : Opens (X : TopCat)) (V : (Over U)ᵒᵖ)
    (g : Γ(X, V.unop.left)) :
    RingCat.Hom.hom ((((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} U).map
      (frobeniusRingSheafOnOpensHom X p hX)).hom.app V) g = g ^ p := by
  rw [overPullback_map_hom_app]
  exact frobeniusPresheafHom_app_apply X p hX V.unop.left g

end AlgebraicGeometry

end

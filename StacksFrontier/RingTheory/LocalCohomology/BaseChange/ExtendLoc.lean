module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.LocalizationColimit

/-!
# Extension of scalars commutes with localization away from an element

Let `f : A →+* B` be a homomorphism of commutative rings, let `a ∈ A` and put `b = f a`. Then
`B ⊗_A M[1/a] = (B ⊗_A M)[1/b]`, naturally in the `A`-module `M`.

## Main definitions

* `Stacks.LocalCohomology.locFunctor`: localization away from `a`, as an endofunctor of
  `ModuleCat A`.
* `Stacks.LocalCohomology.extendLocIso`: the isomorphism `B ⊗_A M[1/a] ≅ (B ⊗_A M)[1/b]`.
* `Stacks.LocalCohomology.extendLocNatIso`: the natural isomorphism
  `(-)[1/a] ⋙ (B ⊗_A -) ≅ (B ⊗_A -) ⋙ (-)[1/b]`.

## References

* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedTensor

universe uA uB v

namespace Stacks.LocalCohomology

section Functor

universe u w

variable {A : Type u} [CommRing A]

/-- Localization away from `a`, as an endofunctor of `ModuleCat A`. -/
@[reducible]
def locFunctor (a : A) : ModuleCat.{max u w} A ⥤ ModuleCat.{max u w} A where
  obj M := locObj a M
  map {M N} g := ModuleCat.ofHom (IsLocalizedModule.map (Submonoid.powers a)
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) g.hom)
  map_id _ := ModuleCat.hom_ext (IsLocalizedModule.map_id _ _)
  map_comp g h := ModuleCat.hom_ext (IsLocalizedModule.map_comp' _ _ _ _ g.hom h.hom)

/-- Localization away from `a` is an additive functor. -/
instance locFunctor_additive (a : A) : (locFunctor.{u, w} a).Additive where
  map_add {M N} g h := ModuleCat.hom_ext (map_add (IsLocalizedModule.map (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) N)) g.hom h.hom)

/-- `Stacks.LocalCohomology.locFunctor a` sends `M` to `M[1/a]`. -/
@[simp]
lemma locFunctor_obj (a : A) (M : ModuleCat.{max u w} A) :
    (locFunctor.{u, w} a).obj M = locObj a M := rfl

/-- The localization of `g : M ⟶ N` away from `a` sends `m / s` to `g m / s`. -/
lemma locFunctor_map_mk (a : A) {M N : ModuleCat.{max u w} A} (g : M ⟶ N) (m : M)
    (s : Submonoid.powers a) :
    ((locFunctor.{u, w} a).map g).hom (LocalizedModule.mk m s) =
      LocalizedModule.mk (g.hom m) s := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  exact IsLocalizedModule.map_mk' _ _ _ g.hom m s

/-- The `n`-th leg of the colimit presentation is natural in the module. -/
lemma locLeg_naturality (a : A) {M N : ModuleCat.{max u w} A} (g : M ⟶ N) (n : ℕ) :
    g ≫ locLeg a N n = locLeg a M n ≫ (locFunctor.{u, w} a).map g := by
  apply ModuleCat.hom_ext
  ext m
  change (locLeg a N n).hom (g.hom m) = ((locFunctor.{u, w} a).map g).hom ((locLeg a M n).hom m)
  rw [locLeg_apply, locLeg_apply, locFunctor_map_mk]

end Functor

section BaseChange

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)

/-- Extension of scalars turns multiplication by `c` into multiplication by `f c`. -/
lemma extendScalars_map_smulHom (c : A) (M : ModuleCat.{max uA uB v} A) :
    (extensionScalars.{uA, uB, v} f).map (smulHom.{uA, max uB v} c M) =
      smulHom.{uB, max uA v} (f c) ((extensionScalars.{uA, uB, v} f).obj M) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let := f.toAlgebra
  change (1 : B) ⊗ₜ[A] (c • m) = f c • ((1 : B) ⊗ₜ[A] m)
  rw [show f c • ((1 : B) ⊗ₜ[A] (m : M)) = (f c * 1) ⊗ₜ[A] (m : M) from rfl, mul_one,
    ← TensorProduct.smul_tmul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]

/-- Extension of scalars carries the multiplication-by-`a` sequence on `M` to the
multiplication-by-`f a` sequence on `B ⊗_A M`. -/
def mulSeqExtendIso (a : A) (M : ModuleCat.{max uA uB v} A) :
    mulSeq.{uA, max uB v} a M ⋙ extensionScalars.{uA, uB, v} f ≅
      mulSeq.{uB, max uA v} (f a) ((extensionScalars.{uA, uB, v} f).obj M) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro i j φ
    rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    change (extensionScalars.{uA, uB, v} f).map (smulHom.{uA, max uB v} (a ^ (j - i)) M) = _
    rw [extendScalars_map_smulHom, map_pow])

/-- `B ⊗_A M[1/a] = (B ⊗_A M)[1/f a]`. -/
def extendLocIso (a : A) (M : ModuleCat.{max uA uB v} A) :
    (extensionScalars.{uA, uB, v} f).obj (locObj.{uA, max uB v} a M) ≅
      locObj.{uB, max uA v} (f a) ((extensionScalars.{uA, uB, v} f).obj M) :=
  IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves (extensionScalars.{uA, uB, v} f)
      (isColimitLocCocone.{uA, max uB v} a M))
    (isColimitLocCocone.{uB, max uA v} (f a) ((extensionScalars.{uA, uB, v} f).obj M))
    (mulSeqExtendIso.{uA, uB, v} f a M)

/-- Extension of scalars of the `n`-th leg of the colimit presentation of `M[1/a]`, followed by
`Stacks.LocalCohomology.extendLocIso`, is the `n`-th leg of the colimit presentation of
`(B ⊗_A M)[1/f a]`. -/
lemma extendLoc_leg (a : A) (M : ModuleCat.{max uA uB v} A) (n : ℕ) :
    (extensionScalars.{uA, uB, v} f).map (locLeg.{uA, max uB v} a M n) ≫
        (extendLocIso.{uA, uB, v} f a M).hom =
      locLeg.{uB, max uA v} (f a) ((extensionScalars.{uA, uB, v} f).obj M) n :=
  (IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves (extensionScalars.{uA, uB, v} f)
      (isColimitLocCocone.{uA, max uB v} a M))
    (isColimitLocCocone.{uB, max uA v} (f a) ((extensionScalars.{uA, uB, v} f).obj M))
    (mulSeqExtendIso.{uA, uB, v} f a M) n).trans
    ((Category.id_comp _).trans (locCocone_ι_app _ _ n))

/-- Extension of scalars along `f` commutes with localization away from `a`: the natural
isomorphism `(-)[1/a] ⋙ (B ⊗_A -) ≅ (B ⊗_A -) ⋙ (-)[1/f a]`. -/
def extendLocNatIso (a : A) :
    locFunctor.{uA, max uB v} a ⋙ extensionScalars.{uA, uB, v} f ≅
      extensionScalars.{uA, uB, v} f ⋙ locFunctor.{uB, max uA v} (f a) :=
  NatIso.ofComponents (fun M ↦ extendLocIso.{uA, uB, v} f a M) (by
    intro M N g
    refine (isColimitOfPreserves (extensionScalars.{uA, uB, v} f)
      (isColimitLocCocone.{uA, max uB v} a M)).hom_ext (fun n ↦ ?_)
    change (extensionScalars.{uA, uB, v} f).map (locLeg.{uA, max uB v} a M n) ≫
        (locFunctor.{uA, max uB v} a ⋙ extensionScalars.{uA, uB, v} f).map g ≫
          (extendLocIso.{uA, uB, v} f a N).hom =
      (extensionScalars.{uA, uB, v} f).map (locLeg.{uA, max uB v} a M n) ≫
        (extendLocIso.{uA, uB, v} f a M).hom ≫
          (extensionScalars.{uA, uB, v} f ⋙ locFunctor.{uB, max uA v} (f a)).map g
    rw [reassoc_of% extendLoc_leg, Functor.comp_map,
      ← Functor.map_comp_assoc, ← locLeg_naturality, Functor.map_comp_assoc, extendLoc_leg,
      locLeg_naturality, Functor.comp_map])

end BaseChange

end Stacks.LocalCohomology

end

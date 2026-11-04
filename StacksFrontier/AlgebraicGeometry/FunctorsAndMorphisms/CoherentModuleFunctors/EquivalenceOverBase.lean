module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceReconstruction
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-!
# Equivalences of categories of coherent modules over a common base ring

Let `R` be a commutative ring and let `X` and `Y` be Noetherian schemes over `R`. Tag 0GPK
describes an equivalence `F : Coh(𝒪_X) ⥤ Coh(𝒪_Y)` as `𝓕 ↦ f^*𝓕 ⊗ ℒ` for an isomorphism of
schemes `f : Y ⟶ X` and an invertible `𝒪_Y`-module `ℒ`. This file refines that description:
when `F` is linear over `R`, the isomorphism `f` can be taken to be a morphism over `R`, that
is `f ≫ (X → Spec R) = (Y → Spec R)`.

## The recovered setup of Tag 0GPK

Tag 0GPK, available here as
`AlgebraicGeometry.CoherentModuleFunctors.exists_iso_pullbackTensor`, takes two Noetherian
schemes `X` and `Y` and an equivalence of categories `F : Coh(𝒪_X) ⥤ Coh(𝒪_Y)`, and produces
an isomorphism of schemes `f : Y ≅ X` together with an invertible `𝒪_Y`-module `ℒ` and a
natural isomorphism `f^*𝓕 ⊗ ℒ ≅ F(𝓕)`, read after the fully faithful inclusions of the
coherent modules into all `𝒪`-modules.

## The argument

The scalar action of `R` on `𝒪_X`-modules is `AlgebraicGeometry.baseScalar`: an element `r`
of `R` acts on a module by multiplication by the image of `r` in the sections of the structure
sheaf, pulled back along the structure morphism `X → Spec R`. The linear structure it induces
is `AlgebraicGeometry.modulesLinear`.

The inclusion of the coherent modules is `R`-linear, so `R`-linearity of `F` transports along
the natural isomorphism of Tag 0GPK to the composite `𝓕 ↦ f^*𝓕 ⊗ ℒ`. Tensoring by `ℒ` is
itself `R`-linear, and invertibility of `ℒ` makes it an equivalence, hence faithful; so
cancelling it leaves `R`-linearity of `f^*` on the coherent modules. Evaluating that at the
structure sheaf `𝒪_X`, which is coherent because `X` is Noetherian, gives
`f^*(r · 1_{𝒪_X}) = r · 1_{f^*𝒪_X}`.

Transposing this equality along the adjunction between `f^*` and `f_*`, and using that the
comparison `𝒪_X ⟶ f_*𝒪_Y` is the map of structure sheaves underlying `f`, evaluation on the
global section `1` says that the ring map `Γ(X, 𝒪_X) → Γ(Y, 𝒪_Y)` induced by `f` carries the
image of `r` to the image of `r`. Two morphisms to an affine scheme agreeing on global
sections are equal, so `f ≫ (X → Spec R) = (Y → Spec R)`.

## Nothing is carried

Tag 0GPJ, which the proof of Tag 0GPK uses, is proved —
`AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence`, restated
for this chain as
`AlgebraicGeometry.CoherentModuleFunctors.exists_iso_pullbackTensor_quasicoherent` — so it is not a
hypothesis here and the result below is unconditional.

## Main results

* `AlgebraicGeometry.CoherentModuleFunctors.exists_iso_pullbackTensor_over_base`: for
  Noetherian schemes `X` and `Y` over `R` and an `R`-linear equivalence
  `F : Coh(𝒪_X) ⥤ Coh(𝒪_Y)`, the isomorphism of Tag 0GPK is a morphism of schemes over `R`.
* `AlgebraicGeometry.CoherentModuleFunctors.pullback_baseScalar_unit_of_linear`: the step
  that carries the content, namely that an `R`-linear description of `F` as `f^*(-) ⊗ ℒ`
  makes `f^*` preserve the base scalar on the structure sheaf.

## References

* [Stacks Project, Tag 0GPL](https://stacks.math.columbia.edu/tag/0GPL)
* [Stacks Project, Tag 0GPK](https://stacks.math.columbia.edu/tag/0GPK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.SheafOfModules (CoherentModules)

universe u

namespace AlgebraicGeometry.CoherentModuleFunctors

variable (R : Type u) [CommRing R]

/-- The inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` is `R`-linear for the scalar action of a base ring:
the scalar action on the full subcategory is the restriction of the one on all modules. -/
lemma coherentToModules_linear (X : Over (Spec (.of R))) :
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    letI : Linear R X.left.Modules := modulesLinear R X
    (coherentToModules X.left).Linear R :=
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  let : Linear R X.left.Modules := modulesLinear R X
  ⟨fun _ _ => rfl⟩

/-- Tensoring on the right by a module sheaf on a scheme over `R` is `R`-linear: it is
isomorphic, by the symmetry of the tensor product, to tensoring on the left, which is
`R`-linear because the base scalar acts through one tensor factor. -/
lemma tensorRight_linear (Y : Over (Spec (.of R))) (L : Y.left.Modules) :
    letI : Linear R (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.left.sheaf)) :=
      Linear.ofRingMorphism (baseRingToCenter R Y)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.left.sheaf).flip.obj
      (L))).Linear R := by
  let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
  let : Linear R Y.left.Modules := modulesLinear R Y
  let : Linear R (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.left.sheaf)) :=
    Linear.ofRingMorphism (baseRingToCenter R Y)
  let : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.left.sheaf).obj
      (L))).Linear R := tensorLeft_linear R Y L
  exact Functor.linear_of_iso (R := R)
    (F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.left.sheaf).obj L)
    (G := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.left.sheaf).flip.obj L)
    (Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight Y.left.presheaf
      Y.left.ringCatSheaf.2 L)

/-- Tensoring on the right by an invertible module sheaf is an equivalence, hence faithful. -/
instance tensorRightFunctor_isEquivalence {Y : Scheme.{u}} (L : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).flip.obj
      (L))).IsEquivalence :=
  (Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor_iff Y.presheaf
    Y.ringCatSheaf.2 L).mpr
      (Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence Y.presheaf Y.ringCatSheaf.2 L)

/-- Multiplication by a base scalar is the scalar action on the identity. -/
lemma smul_id_eq_baseScalar (X : Over (Spec (.of R))) (r : R)
    (M : SheafOfModules.{u} X.left.ringCatSheaf) :
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    (r • 𝟙 M : M ⟶ M) = (baseScalar R X r).app M := by
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  show (baseRingToCenter R X r).app M ≫ 𝟙 M = _
  rw [Category.comp_id]
  rfl

/-- **The content of Tag 0GPL.** Suppose the equivalence `F` of Tag 0GPK is `R`-linear and is
described, after inclusion into all modules, as `𝓕 ↦ f^*𝓕 ⊗ ℒ` with `ℒ` invertible. Then the
inverse image `f^*` carries multiplication by a base scalar on the structure sheaf of `X` to
multiplication by the same base scalar on its inverse image. -/
lemma pullback_baseScalar_unit_of_linear {X Y : Over (Spec (.of R))}
    [IsNoetherian X.left]
    (F : CoherentModules X.left.ringCatSheaf ⥤ CoherentModules Y.left.ringCatSheaf)
    (f : Y.left ≅ X.left) (L : Y.left.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.left.presheaf Y.left.ringCatSheaf.2 L)
    (θ : coherentToModules X.left ⋙ pullbackTensor f.hom L ≅ F ⋙ coherentToModules Y.left)
    (hF : letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
      letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
      F.Linear R) (r : R) :
    (Scheme.Modules.pullback f.hom).map
        ((baseScalar R X r).app (SheafOfModules.unit X.left.ringCatSheaf)) =
      (baseScalar R Y r).app ((Scheme.Modules.pullback f.hom).obj
        (SheafOfModules.unit X.left.ringCatSheaf)) := by
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
  let : Linear R X.left.Modules := modulesLinear R X
  let : Linear R Y.left.Modules := modulesLinear R Y
  let : Linear R (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.left.sheaf)) :=
    Linear.ofRingMorphism (baseRingToCenter R Y)
  have : F.Linear R := hF
  have : Stacks.SheafOfModules.IsInvertible Y.left.presheaf Y.left.ringCatSheaf.2 L := hL
  have : (coherentToModules X.left).Linear R := coherentToModules_linear R X
  have : (coherentToModules Y.left).Linear R := coherentToModules_linear R Y
  set P := Scheme.Modules.pullback f.hom with hP
  set T := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.left.sheaf).flip.obj (L))
    with hT
  have : T.Linear R := tensorRight_linear R Y L
  -- the structure sheaf of `X`, coherent because `X` is Noetherian
  set OX : X.left.Modules := SheafOfModules.unit X.left.ringCatSheaf with hOX
  have : OX.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent _
  set OXc : CoherentModules X.left.ringCatSheaf := ⟨OX, inferInstance⟩ with hOXc
  -- `R`-linearity transports along the description of `F`
  have hlin : (coherentToModules X.left ⋙ pullbackTensor f.hom L).Linear R :=
    Functor.linear_of_iso (R := R) θ.symm
  have hunit := (Functor.linear_iff R
    (coherentToModules X.left ⋙ pullbackTensor f.hom L)).mp hlin OXc r
  have hTlin := (Functor.linear_iff R T).mp ‹T.Linear R› (P.obj OX) r
  -- cancel the tensor factor, which is faithful
  rw [← smul_id_eq_baseScalar R X r OX, ← smul_id_eq_baseScalar R Y r (P.obj OX)]
  exact Functor.map_injective T (hunit.trans hTlin.symm)

/-- Restriction along `⊤ ≤ ⊤` acts as the identity on the sections of the structure sheaf of a
scheme over the whole space. -/
lemma ringCatSheaf_map_leTop (X : Scheme.{u}) :
    X.ringCatSheaf.obj.map (Opens.leTop (⊤ : X.Opens)).op = 𝟙 _ := by
  rw [show Opens.leTop (⊤ : X.Opens) = 𝟙 _ from Subsingleton.elim _ _]
  simp

/-- The image of a base scalar in the global sections of the structure sheaf is the image of
that scalar under the ring map induced by the structure morphism. -/
lemma baseRingToSections_top (X : Over (Spec (.of R))) (r : R) :
    baseRingToSections R X (Opposite.op (⊤ : X.left.Opens)) r =
      (X.hom.appTop).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
  simp [baseRingToSections, ringCatSheaf_map_leTop X.left]
  rfl

/-- **The refinement of Tag 0GPK asserted by Tag 0GPL.** If the inverse image along an
isomorphism `f : Y ≅ X` of schemes over `R` carries the action of every base scalar on the
structure sheaf of `X` to its action on the inverse image, then `f` is a morphism of schemes
over `R`.

Transposing the hypothesis along the adjunction between the inverse and direct image produces
a commuting square with the comparison `𝒪_X ⟶ f_*𝒪_Y`. That comparison is the map of structure
sheaves underlying `f`, so evaluating the square on the global section `1` says that the ring
map `Γ(X, 𝒪_X) → Γ(Y, 𝒪_Y)` induced by `f` carries the image of `r` to the image of `r`. Two
morphisms to an affine scheme that agree on global sections are equal. -/
lemma eq_comp_of_pullback_baseScalar_unit {X Y : Over (Spec (.of R))} (f : Y.left ≅ X.left)
    (h : ∀ r : R, (Scheme.Modules.pullback f.hom).map
          ((baseScalar R X r).app (SheafOfModules.unit X.left.ringCatSheaf)) =
        (baseScalar R Y r).app ((Scheme.Modules.pullback f.hom).obj
          (SheafOfModules.unit X.left.ringCatSheaf))) :
    f.hom ≫ X.hom = Y.hom := by
  let OX : X.left.Modules := SheafOfModules.unit X.left.ringCatSheaf
  let OY : Y.left.Modules := SheafOfModules.unit Y.left.ringCatSheaf
  let φ := f.hom.toRingCatSheafHom
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f.hom
  let v : OX ⟶ (Scheme.Modules.pushforward f.hom).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit φ
  let u := (adj.homEquiv OX OY).symm v
  have huv : adj.homEquiv OX OY u = v := Equiv.apply_symm_apply _ _
  -- the hypothesis, pushed along the comparison `f^*𝒪_X ⟶ 𝒪_Y`
  have hu (r : R) :
      (Scheme.Modules.pullback f.hom).map (show OX ⟶ OX from (baseScalar R X r).app OX) ≫ u =
        u ≫ (show OY ⟶ OY from (baseScalar R Y r).app OY) := by
    rw [h r]
    exact ((baseScalar R Y r).naturality u).symm
  -- its transpose along the adjunction
  have hadj (r : R) : (show OX ⟶ OX from (baseScalar R X r).app OX) ≫ v =
      v ≫ (Scheme.Modules.pushforward f.hom).map
        (show OY ⟶ OY from (baseScalar R Y r).app OY) := by
    have h2 := congrArg (adj.homEquiv OX OY) (hu r)
    rwa [adj.homEquiv_naturality_left (show OX ⟶ OX from (baseScalar R X r).app OX) u,
      adj.homEquiv_naturality_right u (show OY ⟶ OY from (baseScalar R Y r).app OY), huv] at h2
  let UtopX : X.left.Opensᵒᵖ := Opposite.op (⊤ : X.left.Opens)
  let UtopY : Y.left.Opensᵒᵖ := Opposite.op (⊤ : Y.left.Opens)
  -- evaluating the square on the global section `1`
  have hsections (r : R) :
      (f.hom.appTop).hom (baseRingToSections R X UtopX r) = baseRingToSections R Y UtopY r := by
    let : CommRing (X.left.ringCatSheaf.obj.obj UtopX) :=
      inferInstanceAs (CommRing (X.left.presheaf.obj UtopX))
    let one : ↑(OX.val.obj UtopX) := (1 : X.left.ringCatSheaf.obj.obj UtopX)
    have h3 := congrArg (fun g : OX ⟶ (Scheme.Modules.pushforward f.hom).obj OY =>
      (g.app (⊤ : X.left.Opens)).hom one) (hadj r)
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
      Scheme.Modules.pushforward_map_app f.hom
      (show OY ⟶ OY from (baseScalar R Y r).app OY) (⊤ : X.left.Opens)] at h3
    dsimp only [Scheme.Modules.Hom.app] at h3
    dsimp [v, φ] at h3
    change ((SheafOfModules.unitToPushforwardObjUnit
        (Scheme.Hom.toRingCatSheafHom f.hom)).val.app UtopX)
        (((baseScalar R X r).app OX).val.app UtopX one) =
      (((baseScalar R Y r).app OY).val.app UtopY)
        ((SheafOfModules.unitToPushforwardObjUnit
          (Scheme.Hom.toRingCatSheafHom f.hom)).val.app UtopX one) at h3
    have honeX : baseRingToSections R X UtopX r =
        (((baseScalar R X r).app OX).val.app UtopX).hom one := (mul_one _).symm
    refine Eq.trans (congrArg _ honeX) (h3.trans ?_)
    show Mul.mul (baseRingToSections R Y UtopY r)
        ((CommRingCat.Hom.hom (Scheme.Hom.appTop f.hom)) 1) =
      baseRingToSections R Y UtopY r
    exact (congrArg (Mul.mul (baseRingToSections R Y UtopY r))
      (map_one (CommRingCat.Hom.hom (Scheme.Hom.appTop f.hom)))).trans (mul_one _)
  apply AlgebraicGeometry.ext_to_Spec
  ext r
  show ((Scheme.ΓSpecIso (.of R)).inv ≫ (f.hom ≫ X.hom).appTop).hom r =
    ((Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom r
  rw [Scheme.Hom.comp_appTop]
  show (f.hom.appTop).hom ((X.hom.appTop).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) =
    (Y.hom.appTop).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)
  rw [← baseRingToSections_top R X r, ← baseRingToSections_top R Y r]
  simpa [RingCat.id_apply, RingCat.hom_id] using hsections r

/-! ### Tag 0GPL -/

/-- **Stacks Project, Tag 0GPL.** Let `R` be a commutative ring, let `X` and `Y` be Noetherian
schemes over `R`, and let `F : Coh(𝒪_X) ⥤ Coh(𝒪_Y)` be an equivalence of categories which is
linear over `R`. Then the isomorphism of schemes `f : Y ≅ X` and the invertible `𝒪_Y`-module
`ℒ` of Tag 0GPK with `F(𝓕) = f^*𝓕 ⊗ ℒ` may be chosen with `f` a morphism of schemes over `R`,
that is with `f ≫ (X → Spec R) = (Y → Spec R)`.

Nothing is hypothesised. Tag 0GPK is unconditional, so the content here is only the refinement
over `R`: `R`-linearity of `F` forces `f` to be a morphism over `R`. -/
@[stacks 0GPL]
theorem exists_iso_pullbackTensor_over_base (X Y : Over (Spec (.of R)))
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (F : CoherentModules X.left.ringCatSheaf ⥤ CoherentModules Y.left.ringCatSheaf)
    [F.IsEquivalence] :
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
    F.Linear R →
      ∃ (f : Y.left ≅ X.left) (L : Y.left.Modules),
        Stacks.SheafOfModules.IsInvertible Y.left.presheaf Y.left.ringCatSheaf.2 L ∧
        Nonempty (coherentToModules X.left ⋙ pullbackTensor f.hom L ≅
          F ⋙ coherentToModules Y.left) ∧
        f.hom ≫ X.hom = Y.hom := by
  intro hF
  obtain ⟨f, L, hL, ⟨θ⟩⟩ := exists_iso_pullbackTensor F
  exact ⟨f, L, hL, ⟨θ⟩, eq_comp_of_pullback_baseScalar_unit R f
    fun r => pullback_baseScalar_unit_of_linear R F f L hL θ hF r⟩

end AlgebraicGeometry.CoherentModuleFunctors

end

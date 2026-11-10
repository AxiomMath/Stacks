module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusSheafMap
public import StacksFrontier.AlgebraicGeometry.FunctionField.SectionsIntersectionStalks
public import StacksFrontier.Topology.Sheaves.RestrictExtendOpen
public import StacksFrontier.Homology.DerivedIndexing.PullbackFirstDerivedMono
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# `H¹(X, π_* 𝒪_Y)` injects into `H¹(X, j_* j⁻¹ π_* 𝒪_Y)`

Let `π : Y ⟶ X` be a finite surjective morphism of normal integral schemes whose function fields
`K ⊆ L` have characteristic `p` and satisfy `Lᵖ ⊆ K`, and let `U ⊆ X` be a nonempty open. Write
`ℳ = π_* 𝒪_Y` and `ℳ' = j_* j⁻¹ ℳ` (sections `W ↦ ℳ(W ∩ U)`), and likewise `𝒪' = j_* j⁻¹ 𝒪_X`.
The `p`-th power maps form a square of abelian sheaves

```
ℳ  ───▶ ℳ'
│ᵖ      │ᵖ
▼       ▼
𝒪_X ──▶ 𝒪'
```

which is a pullback: a section `s` of `𝒪_Y` over `π⁻¹(W ∩ U)` with `sᵖ` a section of `𝒪_X` over
`W` is integral over every local ring of `Y` at a point of `π⁻¹ W`, hence a section of `𝒪_Y`
over `π⁻¹ W`, because `Y` is normal. So if `H¹(X, 𝒪_X) = 0` and `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_X)` is
surjective, the map `H¹(X, ℳ) ⟶ H¹(X, ℳ')` of abelian sheaf cohomology is injective
(`Stacks.DerivedIndexing.mono_rightDerived_one_map_of_isPullback`).

## Main results

* `CategoryTheory.Sheaf.isPullback_of_forall_app`: a commutative square of sheaves of abelian
  groups which is a pullback on sections over every object is a pullback.
* `AlgebraicGeometry.SeparableGoUp.isPullback_frobeniusHom`: the square above is a pullback.
* `AlgebraicGeometry.SeparableGoUp.mono_rightDerived_one_toRestrictExtend`: the injectivity of
  `H¹(X, ℳ) ⟶ H¹(X, ℳ')`.

## Implementation notes

[Stacks, Tag 0B4U] uses the trace and duality; here the trace is replaced by the `p`-th power
map, and the cohomology class is detected on the open `U` over which `X` is the punctured spectrum.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {F₁ F₂ F₃ F₄ : Sheaf J AddCommGrpCat.{u}} {t : F₁ ⟶ F₂} {l : F₁ ⟶ F₃} {r : F₂ ⟶ F₄}
  {b : F₃ ⟶ F₄}

/-- **A commutative square of sheaves of abelian groups is a pullback when it is one on the
sections over every object**, that is when `(t, l)` is jointly injective and every compatible
pair of sections lifts. -/
theorem isPullback_of_forall_app (w : t ≫ r = l ≫ b)
    (hinj : ∀ (W : Cᵒᵖ) (x y : F₁.obj.obj W), t.hom.app W x = t.hom.app W y →
      l.hom.app W x = l.hom.app W y → x = y)
    (hex : ∀ (W : Cᵒᵖ) (x₂ : F₂.obj.obj W) (x₃ : F₃.obj.obj W),
      r.hom.app W x₂ = b.hom.app W x₃ → ∃ x₁, t.hom.app W x₁ = x₂ ∧ l.hom.app W x₁ = x₃) :
    IsPullback t l r b := by
  have hw : (sheafToPresheaf J AddCommGrpCat.{u}).map t ≫ (sheafToPresheaf J _).map r =
      (sheafToPresheaf J _).map l ≫ (sheafToPresheaf J _).map b := by
    rw [← Functor.map_comp, ← Functor.map_comp, w]
  refine IsPullback.of_map (sheafToPresheaf J AddCommGrpCat.{u}) w
    (IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
      (evaluationJointlyReflectsLimits _ fun W => ?_))
  refine (isLimitMapConePullbackConeEquiv ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj W) hw).symm ?_
  have hwW : t.hom.app W ≫ r.hom.app W = l.hom.app W ≫ b.hom.app W := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app]
    exact congrArg (fun φ : F₁ ⟶ F₄ => φ.hom.app W) w
  have hpb : IsPullback (t.hom.app W) (l.hom.app W) (r.hom.app W) (b.hom.app W) := by
    refine IsPullback.of_map (forget AddCommGrpCat.{u}) hwW ?_
    refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · rw [← Functor.map_comp, ← Functor.map_comp, hwW]
    · rintro x y ⟨h₁, h₂⟩
      exact hinj W x y h₁ h₂
    · intro x₂ x₃ h
      exact hex W x₂ x₃ h
  exact hpb.isLimit

/-- A morphism of sheaves of abelian groups which is injective on sections over every object is a
monomorphism. -/
theorem mono_of_forall_app_injective (h : ∀ W : Cᵒᵖ, Function.Injective (t.hom.app W)) :
    Mono t :=
  have : ∀ W, Mono (((sheafToPresheaf J AddCommGrpCat.{u}).map t).app W) := fun W =>
    (AddCommGrpCat.mono_iff_injective _).mpr (h W)
  (sheafToPresheaf J AddCommGrpCat.{u}).mono_of_mono_map (NatTrans.mono_of_mono_app _)

end CategoryTheory.Sheaf


namespace AlgebraicGeometry.SeparableGoUp

open Stacks.Cohomology.RestrictionCover

/-- The abelian sheaf underlying `π_* 𝒪_Y`. -/
abbrev pushforwardUnitAb {X Y : Scheme.{u}} (π : Y ⟶ X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj
    ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf))

/-- The abelian sheaf underlying `𝒪_X`. -/
abbrev unitAb (X : Scheme.{u}) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)

variable {X Y : Scheme.{u}} (π : Y ⟶ X) (p : ℕ) [Fact p.Prime]
  [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π] [IsNormal X]
  [CharP X.functionField p]
  (hpow : ∀ y : Y.functionField, ∃ k : X.functionField, dominantFunctionFieldMap π k = y ^ p)
  (U : X.Opens) [Nonempty U]

omit [IsFinite π] [Surjective π] [IsNormal X] in
/-- The generic point of `X` lies in `W ∩ U` whenever it lies in `W`. -/
theorem genericPoint_mem_openIntersection {W : X.Opens} (hW : genericPoint X ∈ W) :
    genericPoint X ∈ (openIntersection U).obj W := by
  change genericPoint X ∈ U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W)
  rw [Opens.functor_map_eq_inf]
  exact ⟨hW, Stacks.Divisors.genericPoint_mem_of_nonempty U⟩

omit [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π] [IsNormal X] [Nonempty U] in
/-- The preimage `π⁻¹(W ∩ U)` is contained in `π⁻¹ W`. -/
theorem preimage_openIntersection_le (W : X.Opens) :
    π ⁻¹ᵁ (openIntersection U).obj W ≤ π ⁻¹ᵁ W :=
  fun _ hz => Opens.openIntersection_obj_le U W hz

/-- Restriction of sections of `𝒪_Z` from `W` to a smaller `V` is injective when `V` contains the
generic point whenever `W` does. -/
private theorem restrict_injective_of_genericPoint {Z : Scheme.{u}} [IsIntegral Z] {V W : Z.Opens}
    (hVW : V ≤ W) (hV : genericPoint Z ∈ W → genericPoint Z ∈ V) (x y : Γ(Z, W))
    (h : Z.presheaf.map (homOfLE hVW).op x = Z.presheaf.map (homOfLE hVW).op y) : x = y := by
  refine sections_ext (X := Z) x y fun hW => ?_
  have h1 := congrArg (Z.presheaf.germ _ (genericPoint Z) (hV hW)) h
  rwa [Z.presheaf.germ_res_apply, Z.presheaf.germ_res_apply] at h1

omit [IsFinite π] [IsNormal X] in
/-- Restriction of sections of `𝒪_Y` from `π⁻¹ W` to `π⁻¹(W ∩ U)` is injective. -/
theorem restrict_preimage_openIntersection_injective (W : X.Opens) (x y : Γ(Y, π ⁻¹ᵁ W))
    (h : Y.presheaf.map (homOfLE (preimage_openIntersection_le π U W)).op x =
      Y.presheaf.map (homOfLE (preimage_openIntersection_le π U W)).op y) : x = y :=
  restrict_injective_of_genericPoint (preimage_openIntersection_le π U W)
    (fun hW => genericPoint_mem_preimage π _ (genericPoint_mem_openIntersection U
      (by rwa [← map_genericPoint π]))) x y h

omit [CharP X.functionField p] in
include hpow in
/-- **The extension step.** A section `x₂` of `𝒪_Y` over `π⁻¹(W ∩ U)` whose `p`-th power is
the restriction of a section `x₃` of `𝒪_X` over `W` extends to a section of `𝒪_Y` over `π⁻¹ W`
with `p`-th power `x₃`, because `Y` is normal. -/
theorem exists_extend_of_frobeniusApp_eq [IsNormal Y] (W : X.Opens)
    (x₂ : Γ(Y, π ⁻¹ᵁ (openIntersection U).obj W)) (x₃ : Γ(X, W))
    (h : frobeniusApp π p hpow ((openIntersection U).obj W) x₂ =
      X.presheaf.map (homOfLE (Opens.openIntersection_obj_le U W)).op x₃) :
    ∃ x₁ : Γ(Y, π ⁻¹ᵁ W),
      Y.presheaf.map (homOfLE (preimage_openIntersection_le π U W)).op x₁ = x₂ ∧
        frobeniusApp π p hpow W x₁ = x₃ := by
  have key : ∀ (hW : genericPoint X ∈ W),
      germY π _ (genericPoint_mem_openIntersection U hW) x₂ ^ p =
        Y.presheaf.germ (π ⁻¹ᵁ W) (genericPoint Y) (genericPoint_mem_preimage π W hW)
          (π.app W x₃) := fun hW => by
    rw [← germ_frobeniusApp π p hpow _ (genericPoint_mem_openIntersection U hW), h,
      X.presheaf.germ_res_apply, dominantFunctionFieldMap_germ]
  by_cases hW : genericPoint X ∈ W
  · have : Nonempty (π ⁻¹ᵁ W) := ⟨⟨_, genericPoint_mem_preimage π W hW⟩⟩
    set g := germY π _ (genericPoint_mem_openIntersection U hW) x₂ with hg
    obtain ⟨x₁, hx₁⟩ := exists_germToFunctionField_eq_of_forall_mem_range Y (π ⁻¹ᵁ W) g
      fun y => by
        have : IsIntegrallyClosed (Y.presheaf.stalk y.1) := IsNormal.stalk_normal y.1
        refine IsIntegrallyClosed.isIntegral_iff.mp
          (IsIntegral.of_pow (Fact.out : p.Prime).pos ?_)
        rw [key hW, ← Y.algebraMap_germ_eq_germToFunctionField y.2]
        exact isIntegral_algebraMap
    have hx₁' : Y.presheaf.germ (π ⁻¹ᵁ W) (genericPoint Y) (genericPoint_mem_preimage π W hW)
        x₁ = g := hx₁
    refine ⟨x₁, ?_, ?_⟩
    · refine sections_ext (X := Y) _ _ fun hW₂ => ?_
      rw [Y.presheaf.germ_res_apply]
      exact hx₁'
    · refine sections_ext_of_map π _ _ fun hW₂ => ?_
      rw [germ_frobeniusApp, germY, hx₁', key hW, dominantFunctionFieldMap_germ]
  · refine ⟨0, sections_ext (X := Y) _ _ fun hW₂ => absurd ?_ hW,
      sections_ext (X := X) _ _ fun hW₂ => absurd hW₂ hW⟩
    rw [← map_genericPoint π]
    exact preimage_openIntersection_le π U W hW₂

include hpow in
/-- **The `p`-th power square is a pullback.** For `Y` normal, a section of `𝒪_Y` over
`π⁻¹(W ∩ U)` whose `p`-th power extends to a section of `𝒪_X` over `W` extends to `π⁻¹ W`. -/
theorem isPullback_frobeniusHom [IsNormal Y] :
    IsPullback ((Opens.toRestrictExtend U AddCommGrpCat.{u}).app (pushforwardUnitAb π))
      (frobeniusHom π p hpow) ((Opens.restrictExtend U AddCommGrpCat.{u}).map
        (frobeniusHom π p hpow))
      ((Opens.toRestrictExtend U AddCommGrpCat.{u}).app (unitAb X)) :=
  Sheaf.isPullback_of_forall_app
    ((Opens.toRestrictExtend U AddCommGrpCat.{u}).naturality (frobeniusHom π p hpow)).symm
    (fun W x y hxy _ => restrict_preimage_openIntersection_injective π U W.unop x y hxy)
    (fun W x₂ x₃ h => exists_extend_of_frobeniusApp_eq π p hpow U W.unop x₂ x₃ h)

omit [IsFinite π] [IsNormal X] in
/-- The restriction `ℳ ⟶ j_* j⁻¹ ℳ` for `ℳ = π_* 𝒪_Y` is a monomorphism. -/
theorem mono_toRestrictExtend_pushforwardUnitAb :
    Mono ((Opens.toRestrictExtend U AddCommGrpCat.{u}).app (pushforwardUnitAb π)) :=
  Sheaf.mono_of_forall_app_injective fun W x y hxy =>
    restrict_preimage_openIntersection_injective π U W.unop x y hxy

omit [IsFinite π] [Surjective π] [IsNormal X] in
/-- Restriction of sections of `𝒪_X` from `W` to `W ∩ U` is injective. -/
theorem restrict_openIntersection_injective (W : X.Opens) (x y : Γ(X, W))
    (h : X.presheaf.map (homOfLE (Opens.openIntersection_obj_le U W)).op x =
      X.presheaf.map (homOfLE (Opens.openIntersection_obj_le U W)).op y) : x = y :=
  restrict_injective_of_genericPoint (Opens.openIntersection_obj_le U W)
    (genericPoint_mem_openIntersection U) x y h

omit [IsFinite π] [Surjective π] [IsNormal X] in
/-- The restriction `𝒪_X ⟶ j_* j⁻¹ 𝒪_X` is a monomorphism. -/
theorem mono_toRestrictExtend_unitAb :
    Mono ((Opens.toRestrictExtend U AddCommGrpCat.{u}).app (unitAb X)) :=
  Sheaf.mono_of_forall_app_injective fun W x y hxy =>
    restrict_openIntersection_injective U W.unop x y hxy

omit [IsIntegral X] [IsFinite π] [Surjective π] [IsNormal X] [Nonempty U] in
/-- If every section of `𝒪_X` over `U` extends to `X`, then every section of `𝒪_X` over `X ∩ U`
is the restriction of a global section. -/
theorem exists_restrict_openIntersection_top_eq
    (hext : Function.Surjective (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op))
    (t : Γ(X, (openIntersection U).obj ⊤)) :
    ∃ s : Γ(X, ⊤), X.presheaf.map (homOfLE (Opens.openIntersection_obj_le U ⊤)).op s = t := by
  have he : (openIntersection U).obj ⊤ = U := by
    change U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj ⊤) = U
    rw [Opens.functor_map_eq_inf, top_inf_eq]
  have key : ∀ (V : X.Opens) (hV : V = U) (t : Γ(X, V)),
      ∃ s : Γ(X, ⊤), X.presheaf.map (homOfLE (hV.le.trans le_top)).op s = t := by
    rintro V rfl t
    exact hext t
  exact key _ he t

/-- Global sections of abelian sheaves on `X`. -/
abbrev sectionsAb (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)

include hpow in
/-- **`H¹(X, π_* 𝒪_Y) ⟶ H¹(X, j_* j⁻¹ π_* 𝒪_Y)` is injective** when `H¹(X, 𝒪_X) = 0` and every
function on `U` extends to `X`, for `Y` normal. -/
theorem mono_rightDerived_one_toRestrictExtend [IsNormal Y]
    (hX : IsZero (((sectionsAb X).rightDerived 1).obj (unitAb X)))
    (hext : Function.Surjective (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) :
    Mono (((sectionsAb X).rightDerived 1).map
      ((Opens.toRestrictExtend U AddCommGrpCat.{u}).app (pushforwardUnitAb π))) := by
  have := mono_toRestrictExtend_pushforwardUnitAb π U
  have := mono_toRestrictExtend_unitAb U
  refine Stacks.DerivedIndexing.mono_rightDerived_one_map_of_isPullback (sectionsAb X)
    (isPullback_frobeniusHom π p hpow U) hX ?_
  rw [AddCommGrpCat.epi_iff_surjective]
  exact fun t => exists_restrict_openIntersection_top_eq U hext t

end AlgebraicGeometry.SeparableGoUp

end

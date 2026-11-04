module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentCechVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Čech vanishing for a quasi-coherent module with sections above the universe of its rings

Let `X` be an algebraic space over a scheme `S` and let `G` be a quasi-coherent `𝒪_X`-module on
the small étale site of `X` whose sections live in the universe `u + 1` of the étale charts — one
universe above the rings `Γ(V, 𝒪)` they are modules over. This file proves that **the Čech
cohomology of the underlying abelian presheaf of `G` vanishes in positive degrees on every
finite covering family, by affine charts, of an affine chart.**

The proof is the one of
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_comparisonCoefficients` (which does the
same for a module on the ringed spaces-étale site), with the coefficients taken
to be the sections of `G` itself: the Čech criterion
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_of_isoAtFibreProducts_baseChange` asks
for a comparison `a ⊗ x ↦ a • x|_V` of the coefficients with the base-change presheaf
`V ↦ Γ(V, 𝒪) ⊗_{Γ(W, 𝒪)} G(W)` which is invertible at the iterated fibre products of the family,
and invertibility on affine charts is cartesianness of `G`, the forward half of Descent,
Proposition 03DX (2) at an arbitrary universe of module sections
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse`).

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.moduleCoefficients`: the underlying abelian presheaf of `G`.
* `AlgebraicGeometry.Space.SmallEtale.moduleBaseChangeComparison`: the comparison
  `a ⊗ x ↦ a • x|_V` on the slice at an affine chart.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_moduleCoefficients`: **the Čech
  vanishing.**

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (G : Modules.{u, u + 1} B S hS X.obj X.property)

/-- The slice of the small étale site at a chart has finite limits; local, as in
`StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentCechVanishing`. -/
local instance hasFiniteLimits_overChartOfModule (U : SmallEtale B S hS X.obj) :
    HasFiniteLimits (Over U) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- **The coefficients**: the underlying abelian presheaf of `G`. -/
abbrev moduleCoefficients : (SmallEtale B S hS X.obj)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  ((SheafOfModules.toSheaf _).obj G).obj

/-- The sections of `G` over a chart. -/
abbrev moduleSections (V : SmallEtale B S hS X.obj) : Type (u + 1) :=
  G.val.obj (op V)

/-- The sections of `G` over a chart are a module over the coordinate ring of the chart's
scheme, which is the ring of sections of the structure sheaf over the chart. -/
instance moduleModuleSections (V : SmallEtale B S hS X.obj) :
    Module (Γ(chartScheme V, ⊤) : Type u) (moduleSections B S hS X G V) :=
  inferInstanceAs (Module (chartRing B S hS X.obj X.property V) (G.val.obj (op V)))

/-- Restriction of sections of `G` along a morphism of étale charts. -/
def moduleSectionsRestrict {V V' : SmallEtale B S hS X.obj} (g : V' ⟶ V) :
    moduleSections B S hS X G V →+ moduleSections B S hS X G V' :=
  AddMonoidHom.mk' (fun m => (moduleCoefficients B S hS X G).map g.op m)
    (fun x y => map_add _ x y)

/-- Restriction of sections along `g` is the map of the underlying abelian presheaf of `G` at
`g`. -/
theorem moduleSectionsRestrict_apply {V V' : SmallEtale B S hS X.obj} (g : V' ⟶ V)
    (m : moduleSections B S hS X G V) :
    moduleSectionsRestrict B S hS X G g m = (moduleCoefficients B S hS X G).map g.op m := rfl

/-- Restricting sections along `g` and then along `h` is restriction along `h ≫ g`. -/
theorem moduleSectionsRestrict_comp {V V' V'' : SmallEtale B S hS X.obj} (g : V' ⟶ V)
    (h : V'' ⟶ V') (m : moduleSections B S hS X G V) :
    moduleSectionsRestrict B S hS X G h (moduleSectionsRestrict B S hS X G g m) =
      moduleSectionsRestrict B S hS X G (h ≫ g) m := by
  show ((moduleCoefficients B S hS X G).map g.op ≫
    (moduleCoefficients B S hS X G).map h.op) m = _
  rw [← (moduleCoefficients B S hS X G).map_comp, ← op_comp]
  rfl

/-- **The restriction maps of `G` are semilinear** over pullback of regular functions along the
underlying morphism of schemes. -/
theorem moduleSectionsRestrict_smul {V V' : SmallEtale B S hS X.obj} (g : V' ⟶ V)
    (a : (Γ(chartScheme V, ⊤) : Type u)) (x : moduleSections B S hS X G V) :
    moduleSectionsRestrict B S hS X G g (a • x) =
      ((chartSchemeMap g).appTop).hom a • moduleSectionsRestrict B S hS X G g x :=
  PresheafOfModules.map_smul G.val g.op a x

section Slice

variable {W : SmallEtale B S hS X.obj} [IsAffine (chartScheme W)]

/-- The module structure over the coordinate ring of the terminal object of the slice at `W`. -/
local instance moduleTerminalOverModuleSections :
    Module (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u)
      (moduleSections B S hS X G W) :=
  inferInstanceAs (Module (Γ(chartScheme W, ⊤) : Type u) (moduleSections B S hS X G W))

/-- The module structure on the sections over an object of the slice, in the coordinate-algebra
spelling. -/
instance moduleSliceAlgModuleSections (Zo : (Over W)ᵒᵖ) :
    Module (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo : Type u)
      (moduleSections B S hS X G Zo.unop.left) :=
  moduleModuleSections B S hS X G Zo.unop.left

/-- The bilinear data of the comparison: `(a, x) ↦ a • x|_V`. -/
def moduleBaseChangeBilin (Zo : (Over W)ᵒᵖ) :
    (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo : Type u) →+
      (moduleSections B S hS X G W →+ moduleSections B S hS X G Zo.unop.left) where
  toFun a :=
    { toFun := fun m => a • moduleSectionsRestrict B S hS X G Zo.unop.hom m
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' := fun x y => by simp only [map_add, smul_add] }
  map_zero' := AddMonoidHom.ext fun m => zero_smul _ _
  map_add' a b := AddMonoidHom.ext fun m => add_smul _ _ _

/-- The bilinear data of the comparison sends `(a, m)` to `a • m|_V`. -/
theorem moduleBaseChangeBilin_apply (Zo : (Over W)ᵒᵖ)
    (a : (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo : Type u))
    (m : moduleSections B S hS X G W) :
    moduleBaseChangeBilin B S hS X G Zo a m =
      a • moduleSectionsRestrict B S hS X G Zo.unop.hom m := rfl

/-- **The bilinear data is balanced over the base ring.** -/
theorem moduleBaseChangeBilin_balanced (Zo : (Over W)ᵒᵖ)
    (c : ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
    (a : (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo : Type u))
    (m : moduleSections B S hS X G W) :
    moduleBaseChangeBilin B S hS X G Zo (c • a) m =
      moduleBaseChangeBilin B S hS X G Zo a (c • m) := by
  have hc : moduleSectionsRestrict B S hS X G Zo.unop.hom (c • m) =
      algebraMap (ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
          (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo) c •
        moduleSectionsRestrict B S hS X G Zo.unop.hom m :=
    (moduleSectionsRestrict_smul B S hS X G Zo.unop.hom c.down m).trans
      (congrArg (fun r => r • moduleSectionsRestrict B S hS X G Zo.unop.hom m)
        (overAffineAlgΓBase_algebraMap (terminalOver (chartScheme W))
          ((sliceToOver B S hS X.obj W).obj Zo.unop) c).symm)
  rw [moduleBaseChangeBilin_apply, moduleBaseChangeBilin_apply, hc, Algebra.smul_def, smul_smul,
    mul_comm]

/-- The component of the base-change comparison at an object of the slice. -/
def moduleBaseChangeComparisonApp (Zo : (Over W)ᵒᵖ) :
    ((sliceToOver B S hS X.obj W).op ⋙
        baseChangeAbelianPresheaf (chartScheme W) (moduleSections B S hS X G W)).obj Zo ⟶
      ((Over.forget W).op ⋙ moduleCoefficients B S hS X G).obj Zo :=
  AddCommGrpCat.ofHom (TensorProduct.liftAddHom (moduleBaseChangeBilin B S hS X G Zo)
    (moduleBaseChangeBilin_balanced B S hS X G Zo))

/-- The component of the base-change comparison sends `a ⊗ m` to `a • m|_V`. -/
theorem moduleBaseChangeComparisonApp_tmul (Zo : (Over W)ᵒᵖ)
    (a : (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo : Type u))
    (m : moduleSections B S hS X G W) :
    moduleBaseChangeComparisonApp B S hS X G Zo (a ⊗ₜ m) =
      a • moduleSectionsRestrict B S hS X G Zo.unop.hom m := rfl

/-- **The base-change comparison of `G` on the slice at an affine chart**: the map
`a ⊗ x ↦ a • x|_V` from the base-change presheaf of the sections over `W` to the sections of
`G`. -/
def moduleBaseChangeComparison :
    (sliceToOver B S hS X.obj W).op ⋙
        baseChangeAbelianPresheaf (chartScheme W) (moduleSections B S hS X G W) ⟶
      (Over.forget W).op ⋙ moduleCoefficients B S hS X G where
  app Zo := moduleBaseChangeComparisonApp B S hS X G Zo
  naturality Zo Zo' g := by
    apply AddCommGrpCat.hom_ext
    refine Stacks.Sites.addHom_ext_tmul
      (Rr := ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
      (fun a m => ?_)
    change moduleBaseChangeComparisonApp B S hS X G Zo'
        ((((chartSchemeMap g.unop.left).appTop).hom a) ⊗ₜ m) =
      moduleSectionsRestrict B S hS X G g.unop.left
        (moduleBaseChangeComparisonApp B S hS X G Zo (a ⊗ₜ m))
    have hw : moduleSectionsRestrict B S hS X G g.unop.left
          (moduleSectionsRestrict B S hS X G Zo.unop.hom m) =
        moduleSectionsRestrict B S hS X G Zo'.unop.hom m :=
      (moduleSectionsRestrict_comp B S hS X G Zo.unop.hom g.unop.left m).trans
        (congrArg (fun h => moduleSectionsRestrict B S hS X G h m) (Over.w g.unop))
    refine (moduleBaseChangeComparisonApp_tmul B S hS X G Zo' _ m).trans
      ((congrArg (fun z => (((chartSchemeMap g.unop.left).appTop).hom a) • z) hw.symm).trans
        (moduleSectionsRestrict_smul B S hS X G g.unop.left a
          (moduleSectionsRestrict B S hS X G Zo.unop.hom m)).symm)

/-- **The base-change comparison is bijective at an object of the slice whose chart is affine.**
This is cartesianness of `G` on affine charts (Descent, Proposition 03DX (2), at an arbitrary
universe of module sections), read through `Stacks.RingSquare.tensorMap`, which identifies the
tensor product over the lifted coordinate ring of `W` that the Amitsur side uses with the tensor
product over the ring of sections of the structure sheaf over `W`. -/
theorem bijective_moduleBaseChangeComparisonApp (hG : G.IsQuasicoherentOnSite)
    (Zo : (Over W)ᵒᵖ) (hZ : IsAffine (chartScheme Zo.unop.left)) :
    Function.Bijective (moduleBaseChangeComparisonApp B S hS X G Zo).hom := by
  let f : Zo.unop.left ⟶ W := Zo.unop.hom
  have hbij : Function.Bijective (sectionsBaseChange G f) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse B S hS X.obj X.property G hG
      W Zo.unop.left ‹IsAffine (chartScheme W)› hZ f
  let algWZ : Algebra (chartRing B S hS X.obj X.property W)
      (chartRing B S hS X.obj X.property Zo.unop.left) := chartAlgebra f
  let modWZ : Module (chartRing B S hS X.obj X.property W) (G.val.obj (op Zo.unop.left)) :=
    chartSectionsModule G f
  let eW : ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u) ≃+*
      chartRing B S hS X.obj X.property W :=
    ULift.ringEquiv
  let eZ : (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo : Type u) ≃+*
      chartRing B S hS X.obj X.property Zo.unop.left :=
    RingEquiv.refl _
  let b : chartRing B S hS X.obj X.property W →+* chartRing B S hS X.obj X.property Zo.unop.left :=
    chartRestrict f
  let a := algebraMap (ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
    (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo)
  have hsq : ∀ t, eZ (a t) = b (eW t) := fun t =>
    overAffineAlgΓBase_algebraMap (terminalOver (chartScheme W))
      ((sliceToOver B S hS X.obj W).obj Zo.unop) t
  have hA : ∀ (t : ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
      (c : (sliceAlg (B := B) (S := S) (hS := hS) (Y := X) Zo : Type u)),
      t • c = a t * c := fun t c => Algebra.smul_def t c
  have hB : ∀ (s : chartRing B S hS X.obj X.property W)
      (d : chartRing B S hS X.obj X.property Zo.unop.left), s • d = b s * d := fun s d => rfl
  have hP : ∀ (t : ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
      (x : moduleSections B S hS X G W), t • x = eW t • x := fun t x => rfl
  let T := Stacks.RingSquare.tensorMap a b eW eZ hsq hA hB hP
  have key : (moduleBaseChangeComparisonApp B S hS X G Zo).hom =
      (sectionsBaseChange G f).toAddMonoidHom.comp T := by
    refine Stacks.Sites.addHom_ext_tmul
      (Rr := ULift.{u} (Γ((terminalOver (chartScheme W)).left, ⊤) : Type u))
      (fun c m => ?_)
    exact (moduleBaseChangeComparisonApp_tmul B S hS X G Zo c m).trans
      (chartBaseChange_tmul G f (eZ c) m).symm
  rw [key]
  exact hbij.comp (Stacks.RingSquare.bijective_tensorMap a b eW eZ hsq hA hB hP)

/-- **The base-change comparison is an isomorphism at an object of the slice whose chart is
affine.** -/
theorem isIso_moduleBaseChangeComparisonApp (hG : G.IsQuasicoherentOnSite)
    (Zo : (Over W)ᵒᵖ) (hZ : IsAffine (chartScheme Zo.unop.left)) :
    IsIso (moduleBaseChangeComparisonApp B S hS X G Zo) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_moduleBaseChangeComparisonApp B S hS X G hG Zo hZ)

end Slice

/-- **The Čech cohomology of a quasi-coherent module with sections in the universe of the étale
charts vanishes in positive degrees on a finite affine covering family of an affine chart.** -/
theorem isZero_cechCohomology_moduleCoefficients (hG : G.IsQuasicoherentOnSite)
    {W : SmallEtale B S hS X.obj} (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{u + 1} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS X.obj W)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E (moduleCoefficients B S hS X G) p) :=
  isZero_cechCohomology_of_isoAtFibreProducts_baseChange E hfin haff hcov
    (moduleSections B S hS X G W) (moduleCoefficients B S hS X G)
    (moduleBaseChangeComparison B S hS X G)
    (fun n i => isIso_moduleBaseChangeComparisonApp B S hS X G hG _
      (isAffine_chartScheme_piObj B S hS X.obj hW E haff n i))
    p hp

end SmallEtale

end AlgebraicGeometry.Space

end

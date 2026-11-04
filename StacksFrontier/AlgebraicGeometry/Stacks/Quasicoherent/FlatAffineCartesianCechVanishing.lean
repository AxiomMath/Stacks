module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeCechVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeOfCartesianLargeSections
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingBaseChangeCoefficientsSmallFamilies
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComparisonAtTheFibreProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongASliceFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOverTheTerminalSlice

/-!
# Čech vanishing for modules cartesian on flat affine arrows, at an arbitrary module universe

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
modules over the structure sheaf of **Stacks 06TV**, with sections in an arbitrary universe
`max (u + 1) v w m`, which is *cartesian on flat affine arrows*
(`AlgebraicGeometry.Stack.IsCartesianOnFlatAffineArrows`): along every arrow `φ : z ⟶ y` lying
over a flat morphism of affine schemes, `𝒪(z) ⊗_{𝒪(y)} F(y) ⟶ F(z)` is bijective.  Let `x` lie
over an affine scheme `Y` and let `{x_i → x}` lie over a standard fppf covering `{Y_i → Y}`.
Then `Ȟ^n({x_i → x}, F) = 0` for `n > 0`.

This is the Čech input of the vanishing `H^n(x, F) = 0` (`n > 0`) for the faithful class
`LQCoh^fbc` at module universe `u + 1`, and of the extension step of **Stacks 0771** (2) there.
At module universe `u` the same statement is
`AlgebraicGeometry.Stack.isZero_cechCohomology_of_sheafFlatBaseChange`, which goes through the
quasi-coherent `𝒪_Y`-module below `x`; that module does not exist in Mathlib's
`AlgebraicGeometry.Scheme.Modules` once the sections live in a larger universe, so here the
coefficients are compared directly with the base-change presheaf `V ↦ Γ(V, 𝒪_V) ⊗_{𝒪(x)} F(x)`
of `StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingBaseChangeCoefficients`.

## The argument

* The comparison `Γ(V, 𝒪_V) ⊗_{𝒪(x)} F(x) ⟶ F(z)`, `a ⊗ s ↦ a • s|_z`, for `z ⟶ x` lying over
  `V ⟶ Y`, is natural on the whole slice at `x`
  (`AlgebraicGeometry.Stack.cartesianBaseChangeComparison`) and is the base-change map of the
  restriction along `z ⟶ x`, transported along the universe lift of the base ring
  (`AlgebraicGeometry.Stack.bijective_cartesianBaseChangeComparisonApp`).  So it is invertible
  at every object lying flat over `Y` with affine total space, in particular at the iterated
  fibre products of the family, which lie over the affine flat schemes `Y_{i_0} ×_Y ⋯ ×_Y Y_{i_p}`.
* `Stacks.CechSite.isZero_cechCohomology_of_isoAtFibreProducts` reduces to the Čech cohomology
  of the base-change presheaf read along the slice functor `Over x ⥤ Over Y`, which preserves the
  iterated fibre products; that is the Čech cohomology of the base-change presheaf along the
  standard covering `{Y_i → Y}`, which vanishes by
  `AlgebraicGeometry.isZero_cechCohomology_succ_baseChange_of_smallFamily` (Amitsur, Stacks 023M).

## Main results

* `AlgebraicGeometry.Stack.cartesianBaseChangeComparison`.
* `AlgebraicGeometry.Stack.bijective_cartesianBaseChangeComparisonApp`.
* `AlgebraicGeometry.Stack.isZero_cechCohomology_of_isCartesianOnFlatAffineArrows`: **the Čech
  vanishing.**

No `@[stacks]` attribute is claimed: this is a helper of Stacks 0771 at a module universe the
source does not distinguish.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m t

namespace AlgebraicGeometry.Stack

open Stacks.PresheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  (F : PresheafOfModules.{max u t} (ringStructureSheafCore B S hS p hp τ hτ).obj)

/-! ### Restriction of sections -/

/-- Restriction of the sections of `F` along an arrow of `𝒳`, as an additive map. -/
def cartesianRestrict {z z' : 𝒳} (g : z' ⟶ z) : F.obj (op z) →+ F.obj (op z') :=
  AddMonoidHom.mk' (fun s => (F.map g.op).hom s) (fun a b => map_add _ a b)

/-- Restriction along `g` sends a section `s` to `(F.map g.op) s`. -/
theorem cartesianRestrict_apply {z z' : 𝒳} (g : z' ⟶ z) (s : F.obj (op z)) :
    cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F g s = (F.map g.op).hom s := rfl

/-- Restriction along `g` followed by restriction along `g'` is restriction along `g' ≫ g`. -/
theorem cartesianRestrict_comp {z z' z'' : 𝒳} (g : z' ⟶ z) (g' : z'' ⟶ z')
    (s : F.obj (op z)) :
    cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F g'
        (cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F g s) =
      cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F (g' ≫ g) s := by
  simp only [cartesianRestrict_apply, op_comp, PresheafOfModules.map_comp]
  rfl

/-- **The restriction maps are semilinear** over the restriction maps of the structure sheaf. -/
theorem cartesianRestrict_smul {z z' : 𝒳} (g : z' ⟶ z)
    (a : (ringStructureSheafCore B S hS p hp τ hτ).obj.obj (op z)) (s : F.obj (op z)) :
    cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F g (a • s) =
      ((ringStructureSheafCore B S hS p hp τ hτ).obj.map g.op).hom a •
        cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F g s :=
  PresheafOfModules.map_smul F g.op a s

/-! ### The base-change comparison on the slice at an object over an affine scheme -/

section Slice

variable (x : 𝒳) [IsAffine ((toScheme B S hS p).obj x)]

/-- The module structure on `F(x)` over the coordinate ring of the terminal object of the
slice of schemes over the scheme below `x`, which is the spelling
`AlgebraicGeometry.baseChangeAbelianPresheaf` asks for. -/
instance moduleTerminalOverCartesianSections :
    Module (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u) (F.obj (op x)) :=
  inferInstanceAs
    (Module ((ringStructureSheafCore B S hS p hp τ hτ).obj.obj (op x)) (F.obj (op x)))

/-- The module structure on `F(x)` over the coordinate ring of the scheme below `x`. -/
instance moduleSchemeCartesianSections :
    Module (Γ((toScheme B S hS p).obj x, ⊤) : Type u) (F.obj (op x)) :=
  inferInstanceAs
    (Module ((ringStructureSheafCore B S hS p hp τ hτ).obj.obj (op x)) (F.obj (op x)))

/-- The coordinate algebra of the scheme below an object of the slice at `x`, over the lifted
coordinate ring of the scheme below `x`. -/
abbrev cartesianSliceAlg (Zo : (Over x)ᵒᵖ) :
    CommAlgCat.{u} (ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u)) :=
  ((overAffineAlgΓBase (terminalOver ((toScheme B S hS p).obj x))).obj
    ((Over.post (toScheme B S hS p)).obj Zo.unop)).unop

/-- The module structure on the sections over an object of the slice, in the coordinate-algebra
spelling. -/
instance moduleCartesianSliceAlg (Zo : (Over x)ᵒᵖ) :
    Module (cartesianSliceAlg B S hS p x Zo : Type u) (F.obj (op Zo.unop.left)) :=
  inferInstanceAs (Module ((ringStructureSheafCore B S hS p hp τ hτ).obj.obj (op Zo.unop.left))
    (F.obj (op Zo.unop.left)))

/-- The bilinear data of the comparison: `(a, s) ↦ a • s|_z`. -/
def cartesianBaseChangeBilin (Zo : (Over x)ᵒᵖ) :
    (cartesianSliceAlg B S hS p x Zo : Type u) →+
      (F.obj (op x) →+ F.obj (op Zo.unop.left)) where
  toFun a :=
    (DistribSMul.toAddMonoidHom (F.obj (op Zo.unop.left)) a).comp
      (cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom)
  map_zero' := AddMonoidHom.ext fun _ => zero_smul _ _
  map_add' _ _ := AddMonoidHom.ext fun _ => add_smul _ _ _

/-- The bilinear data of the comparison sends `(a, s)` to `a • s|_z`. -/
theorem cartesianBaseChangeBilin_apply (Zo : (Over x)ᵒᵖ)
    (a : (cartesianSliceAlg B S hS p x Zo : Type u)) (s : F.obj (op x)) :
    cartesianBaseChangeBilin.{u, v, w, t} B S hS p hp τ hτ F x Zo a s =
      a • cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom s := rfl

/-- **The bilinear data is balanced over the base ring**: the lifted coordinate ring of the
scheme below `x` acts on a coordinate algebra by pullback of global sections
(`AlgebraicGeometry.overAffineAlgΓBase_algebraMap`), which is the ring map the restriction maps
of `F` are semilinear over. -/
theorem cartesianBaseChangeBilin_balanced (Zo : (Over x)ᵒᵖ)
    (c : ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u))
    (a : (cartesianSliceAlg B S hS p x Zo : Type u)) (s : F.obj (op x)) :
    cartesianBaseChangeBilin.{u, v, w, t} B S hS p hp τ hτ F x Zo (c • a) s =
      cartesianBaseChangeBilin.{u, v, w, t} B S hS p hp τ hτ F x Zo a (c • s) := by
  have hc : cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom (c • s) =
      algebraMap (ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u))
          (cartesianSliceAlg B S hS p x Zo) c •
        cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom s :=
    (cartesianRestrict_smul.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom c.down s).trans
      (congrArg (fun r => r • cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom s)
        (overAffineAlgΓBase_algebraMap (terminalOver ((toScheme B S hS p).obj x))
          ((Over.post (toScheme B S hS p)).obj Zo.unop) c).symm)
  rw [cartesianBaseChangeBilin_apply, cartesianBaseChangeBilin_apply, hc, Algebra.smul_def,
    smul_smul, mul_comm]

/-- The component of the base-change comparison at an object of the slice at `x`. -/
def cartesianBaseChangeComparisonApp (Zo : (Over x)ᵒᵖ) :
    ((Over.post (toScheme B S hS p)).op ⋙
        baseChangeAbelianPresheaf ((toScheme B S hS p).obj x) (F.obj (op x))).obj Zo ⟶
      ((Over.forget x).op ⋙ F.presheaf).obj Zo :=
  AddCommGrpCat.ofHom (TensorProduct.liftAddHom
    (cartesianBaseChangeBilin.{u, v, w, t} B S hS p hp τ hτ F x Zo)
    (cartesianBaseChangeBilin_balanced.{u, v, w, t} B S hS p hp τ hτ F x Zo))

/-- The component of the base-change comparison at `Zo` sends `a ⊗ₜ s` to `a • s|_z`. -/
theorem cartesianBaseChangeComparisonApp_tmul (Zo : (Over x)ᵒᵖ)
    (a : (cartesianSliceAlg B S hS p x Zo : Type u)) (s : F.obj (op x)) :
    cartesianBaseChangeComparisonApp.{u, v, w, t} B S hS p hp τ hτ F x Zo (a ⊗ₜ s) =
      a • cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom s := rfl

/-- **The base-change comparison on the slice at `x`**: `a ⊗ s ↦ a • s|_z` from the base-change
presheaf of `F(x)`, read along `Over x ⥤ Over Y`, to the sections of `F`.  It is natural on the
whole slice; only its invertibility needs flatness and affineness. -/
def cartesianBaseChangeComparison :
    (Over.post (toScheme B S hS p)).op ⋙
        baseChangeAbelianPresheaf ((toScheme B S hS p).obj x) (F.obj (op x)) ⟶
      (Over.forget x).op ⋙ F.presheaf where
  app Zo := cartesianBaseChangeComparisonApp.{u, v, w, t} B S hS p hp τ hτ F x Zo
  naturality Zo Zo' g := by
    apply AddCommGrpCat.hom_ext
    refine Stacks.Sites.addHom_ext_tmul
      (Rr := ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u))
      (fun a s => ?_)
    change cartesianBaseChangeComparisonApp.{u, v, w, t} B S hS p hp τ hτ F x Zo'
        ((((ringStructureSheafCore B S hS p hp τ hτ).obj.map g.unop.left.op).hom a) ⊗ₜ s) =
      cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F g.unop.left
        (cartesianBaseChangeComparisonApp.{u, v, w, t} B S hS p hp τ hτ F x Zo (a ⊗ₜ s))
    have hw : cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F g.unop.left
          (cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom s) =
        cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo'.unop.hom s :=
      (cartesianRestrict_comp.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom g.unop.left s).trans
        (congrArg (fun h => cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F h s) (Over.w g.unop))
    exact (cartesianBaseChangeComparisonApp_tmul.{u, v, w, t} B S hS p hp τ hτ F x Zo' _ s).trans
      ((congrArg (fun z => (((ringStructureSheafCore B S hS p hp τ hτ).obj.map
          g.unop.left.op).hom a) • z) hw.symm).trans
        (cartesianRestrict_smul.{u, v, w, t} B S hS p hp τ hτ F g.unop.left a
          (cartesianRestrict.{u, v, w, t} B S hS p hp τ hτ F Zo.unop.hom s)).symm)

/-- **The base-change comparison is bijective at an object lying flat over the scheme below `x`
with affine total space**, when `F` is cartesian on flat affine arrows.  It is the base-change
map `restrictionBaseChange` of the restriction along `z ⟶ x`, transported along the universe
lift of the base ring by `Stacks.RingSquare.tensorMap`. -/
theorem bijective_cartesianBaseChangeComparisonApp
    (Zo : (Over x)ᵒᵖ)
    (hbij : Function.Bijective
      (restrictionBaseChange.{v, w, u, t} (R := (structureSheaf B S hS p hp τ hτ).obj) F
        Zo.unop.hom.op)) :
    Function.Bijective
      (cartesianBaseChangeComparisonApp.{u, v, w, t} B S hS p hp τ hτ F x Zo).hom := by
  let O := (structureSheaf B S hS p hp τ hτ).obj
  let modx : Module (O.obj (op x) : Type u) (F.obj (op x)) := (F.obj (op x)).isModule
  let algxz : Algebra (O.obj (op x) : Type u) (O.obj (op Zo.unop.left) : Type u) :=
    ((O.map Zo.unop.hom.op).hom).toAlgebra
  let eW : ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u) ≃+*
      (O.obj (op x) : Type u) :=
    ULift.ringEquiv
  let eZ : (cartesianSliceAlg B S hS p x Zo : Type u) ≃+* (O.obj (op Zo.unop.left) : Type u) :=
    RingEquiv.refl _
  let b := (O.map Zo.unop.hom.op).hom
  let a := algebraMap (ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u))
    (cartesianSliceAlg B S hS p x Zo)
  have hsq : ∀ t, eZ (a t) = b (eW t) :=
    overAffineAlgΓBase_algebraMap (terminalOver ((toScheme B S hS p).obj x))
      ((Over.post (toScheme B S hS p)).obj Zo.unop)
  have hA : ∀ (t : ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u))
      (c : (cartesianSliceAlg B S hS p x Zo : Type u)), t • c = a t * c :=
    Algebra.smul_def
  have hB : ∀ (s : (O.obj (op x) : Type u)) (d : (O.obj (op Zo.unop.left) : Type u)),
      s • d = b s * d := fun s d => rfl
  have hP : ∀ (t : ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u))
      (s : F.obj (op x)), t • s = eW t • s := fun t s => rfl
  let T := Stacks.RingSquare.tensorMap a b eW eZ hsq hA hB hP
  have key : (cartesianBaseChangeComparisonApp.{u, v, w, t} B S hS p hp τ hτ F x Zo).hom =
      (restrictionBaseChange.{v, w, u, t} (R := O) F Zo.unop.hom.op).hom.toAddMonoidHom.comp T :=
    Stacks.Sites.addHom_ext_tmul
      (Rr := ULift.{u} (Γ((terminalOver ((toScheme B S hS p).obj x)).left, ⊤) : Type u))
      fun c s => (cartesianBaseChangeComparisonApp_tmul.{u, v, w, t} B S hS p hp τ hτ F x Zo c
        s).trans (restrictionBaseChange_tmul.{v, w, u, t} (R := O) F Zo.unop.hom.op (eZ c) s).symm
  rw [key]
  exact hbij.comp (Stacks.RingSquare.bijective_tensorMap a b eW eZ hsq hA hB hP)

end Slice

/-! ### The Čech vanishing -/

include hp in
/-- **The Čech cohomology of a module cartesian on flat affine arrows, along a family lying over
a standard fppf covering of an affine scheme, vanishes in positive degrees**, at the module
universe `max (u + 1) v w m`.

The comparison `AlgebraicGeometry.Stack.cartesianBaseChangeComparison` with the base-change
presheaf of `F(x)` is invertible at the iterated fibre products of the family, which lie flat
over the scheme below `x` with affine total space
(`AlgebraicGeometry.Stack.prop_toScheme_map_cechProduct_hom`, for `Flat` and for `IsAffineHom`);
the slice functor `Over x ⥤ Over Y` preserves those fibre products; and the base-change presheaf
has vanishing positive-degree Čech cohomology on the standard covering below,
`AlgebraicGeometry.isZero_cechCohomology_succ_baseChange_of_smallFamily`. -/
theorem isZero_cechCohomology_of_isCartesianOnFlatAffineArrows
    (F : PresheafOfModules.{max (u + 1) v w m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : IsCartesianOnFlatAffineArrows.{u, v, w, m} B S hS p hp τ hτ F)
    {x : 𝒳} [IsAffine ((toScheme B S hS p).obj x)] (𝒰 : PreZeroHypercover.{u} x)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀), HasProduct (fun a ↦ Over.mk (𝒰.f (i a)))]
    (hstd : IsStandardCovering .fppf (fun i ↦ (toScheme B S hS p).obj (𝒰.X i))
      (fun i ↦ (toScheme B S hS p).map (𝒰.f i)))
    (n : ℕ) (hn : 0 < n) :
    IsZero (Stacks.CechSite.cechCohomology 𝒰 F.presheaf n) := by
  classical
  have : MorphismProperty.RespectsIso @Flat := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.IsStableUnderComposition @IsAffineHom :=
    ⟨fun _ _ _ _ ↦ inferInstance⟩
  have : MorphismProperty.RespectsIso @IsAffineHom :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : HasPullbacks 𝒳 := hasPullbacks_fibred B S hS p hp
  set Y := (toScheme B S hS p).obj x
  let : Module (Γ(Y, ⊤) : Type u) (F.obj (op x)) :=
    moduleSchemeCartesianSections.{u, v, w, max (u + 1) v w m} B S hS p hp τ hτ F x
  let : Module (Γ((terminalOver Y).left, ⊤) : Type u) (F.obj (op x)) :=
    moduleTerminalOverCartesianSections.{u, v, w, max (u + 1) v w m} B S hS p hp τ hτ F x
  let v : Over x ⥤ Over Y := Over.post (toScheme B S hS p)
  let G := Stacks.CechSite.sliceImageFamily 𝒰 v
  have : ∀ (m : ℕ) (i : Fin (m + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a))) :=
    fun m i ↦ Stacks.Sites.hasProduct_over_fin m _ (fun _ _ _ ↦ inferInstance)
  have : HasFiniteLimits (Over (Over.mk (𝟙 Y))) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : ∀ (m : ℕ) (i : Fin (m + 1) → (Stacks.CechSite.toTerminalSliceFamily G).I₀),
      HasProduct (fun a ↦ Over.mk ((Stacks.CechSite.toTerminalSliceFamily G).f (i a))) :=
    fun _ _ ↦ inferInstance
  -- the slice functor preserves the iterated fibre products of the family
  have hiso : ∀ (m : ℕ) (i : Fin (m + 1) → 𝒰.I₀),
      IsIso (Stacks.CechSite.cechProductMapOfSliceFunctor 𝒰 v m i) := fun m i ↦ by
    have : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (𝒰.f (i a)))) v :=
      Stacks.Sites.preservesLimit_fibreProducts_overPost (toScheme B S hS p) 𝒰
        (fun _ _ _ ↦ inferInstance) (fun _ _ g ↦ preservesLimit_cospan_toScheme B S hS p hp _ g)
        m i
    exact Stacks.CechSite.isIso_cechProductMapOfSliceFunctor 𝒰 v m i
  -- the vanishing for the base-change presheaf along the standard covering below
  have hslice := Stacks.CechSite.isZero_sliceCechCohomology_of_isZero_of_sliceFunctor 𝒰 v
    (baseChangeAbelianPresheaf Y (F.obj (op x))) hiso n
    (Stacks.CechSite.isZero_sliceCechCohomology_of_isZero_cechCohomology_toTerminalSliceFamily
      G (baseChangeAbelianPresheaf Y (F.obj (op x))) n
      (isZero_cechCohomology_succ_baseChange_of_smallFamily Y (F.obj (op x)) .fppf
        (Stacks.CechSite.toTerminalSliceFamily G) hstd n hn))
  refine Stacks.CechSite.isZero_cechCohomology_of_isoAtFibreProducts 𝒰
    (cartesianBaseChangeComparison.{u, v, w, max (u + 1) v w m} B S hS p hp τ hτ F x)
    (fun m i ↦ ?_) n hslice
  have hflat := prop_toScheme_map_cechProduct_hom B S hS p hp @Flat 𝒰
    (fun j ↦ (hstd.standard j).1) m i
  have haff := prop_toScheme_map_cechProduct_hom B S hS p hp @IsAffineHom 𝒰
    (fun j ↦ by have := hstd.affine_source j; infer_instance) m i
  have hZ : IsAffine ((toScheme B S hS p).obj (∏ᶜ (fun a ↦ Over.mk (𝒰.f (i a)))).left) :=
    isAffine_of_isAffineHom ((toScheme B S hS p).map (∏ᶜ (fun a ↦ Over.mk (𝒰.f (i a)))).hom)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_cartesianBaseChangeComparisonApp.{u, v, w, max (u + 1) v w m} B S hS p hp τ hτ F x _
      (hF _ hflat hZ ‹IsAffine ((toScheme B S hS p).obj x)›))

end AlgebraicGeometry.Stack

end

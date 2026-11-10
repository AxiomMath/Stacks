module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceChartConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineLocallySpannedDischarge
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence

/-!
# Quasi-coherent modules on a fibred category are cartesian between affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `ℱ` a quasi-coherent module on
the associated fppf site `(𝒳, 𝒪_𝒳)`.  For a morphism `g : y ⟶ x` of `𝒳` lying over a morphism of
affine schemes, the base change comparison `𝒪(y) ⊗_{𝒪(x)} ℱ(x) ⟶ ℱ(y)` is bijective: this is the
cartesian half of Stacks 0H0E, read on `𝒳` itself rather than on its affine subcategory.  It is
the input which makes sections over affine objects behave like modules over rings, and this file
uses it to descend finite generation of sections along fppf coverings: a quasi-coherent module of
finite type on `𝒳` has finitely generated sections over every object lying over an affine scheme.

## Main definitions

* `AlgebraicGeometry.Stack.fibredSectionsBaseChange`: the base change comparison of the sections
  of a module on `𝒳` along a morphism, as a linear map over the global functions of the source.
* `AlgebraicGeometry.Stack.IsCartesianBetweenAffines`: all those comparisons between objects over
  affine schemes are bijective.

## Main results

* `AlgebraicGeometry.Stack.isCartesianBetweenAffines_of_isQuasicoherentOnSite`: a quasi-coherent
  module is cartesian between affine objects.
* `AlgebraicGeometry.Stack.mem_span_of_forall_restrict_mem_span_fibred`: membership in a finite
  span descends along a finite fppf covering family by affine objects.
* `AlgebraicGeometry.Stack.moduleFinite_sections_of_isFiniteTypeOnSite_fibred`: the sections over
  an affine object of a module of finite type which is cartesian between affine objects form a
  finite module.
* `AlgebraicGeometry.Stack.hasFiniteGlobalPresentation_over_of_finitePresentation`: a module
  cartesian between affine objects whose sections over an affine object are finitely presented has
  a finite global presentation on the slice at that object.

## Implementation notes

The cartesian property is obtained from
`AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`
(Stacks 0H0E, through Descent, Proposition 03DX) applied to the restriction of the module to the
affine subcategory of Stacks 0H0A, which is quasi-coherent because the affine inclusion is a
cocontinuous dense subsite inclusion (Stacks 0H0B).  The descent arguments follow
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections`, with the étale charts of an
algebraic space replaced by the objects of `𝒳` and the étale coverings by fppf ones; the finite
affine refinement is `AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le` and the
faithful flatness is `AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`.

The module sections are in the universe `u` of the schemes, the universe in which Stacks 0H0E is
available.

## References

* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Stacks.PresheafOfModules

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The presheaf of commutative rings of global functions on the schemes underlying the objects
of a category over the big fppf category of `S`. -/
noncomputable abbrev fibredRings : 𝒳ᵒᵖ ⥤ CommRingCat.{u} :=
  (p ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ

/-- **A quasi-coherent module on a fibred category is cartesian over every morphism between objects
lying over affine schemes**: the comparison `𝒪(y) ⊗_{𝒪(x)} ℱ(x) ⟶ ℱ(y)` is bijective.  This is
the cartesian half of Stacks 0H0E, transported from the affine subcategory. -/
theorem bijective_restrictionBaseChange_fibredRings_of_isQuasicoherentOnSite
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : F.IsQuasicoherentOnSite) {x y : 𝒳} (g : y ⟶ x)
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hy : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y)) :
    Function.Bijective
      (restrictionBaseChange.{v, w, u, u} (R := fibredRings B S hS p) F.val g.op) := by
  have hsc := AffineCategory.inclusion_isSpecialCocontinuous_fppf B S hS p hp
  have := hsc.1
  have := hsc.2
  have hres := Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite
    (J := associatedAffineTopology B S hS p (BigAffineFppf.topology B S hS))
    (K := associatedTopology B S hS p B.topology)
    (AffineCategory.inclusion B S hS p) (ringStructureSheafCore B S hS p hp B.topology le_rfl)
    F hF
  let xa : AffineCategory B S hS p := ⟨x, hx⟩
  let ya : AffineCategory B S hS p := ⟨y, hy⟩
  let ga : ya ⟶ xa := ObjectProperty.homMk g
  have h := AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    B S hS p _ rfl hp .fppf _ _ hres ga.op
  exact (ConcreteCategory.isIso_iff_bijective _).1 h

/-! ### Sections over objects as modules over global functions -/

/-- The ring of global functions on the scheme underlying an object of `𝒳`. -/
noncomputable abbrev fibredSectionRing (x : 𝒳) : Type u :=
  Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)

variable {B S hS p}

/-- Restriction of global functions along a morphism of `𝒳`. -/
noncomputable abbrev fibredSectionRestrict {x y : 𝒳} (g : y ⟶ x) :
    fibredSectionRing B S hS p x →+* fibredSectionRing B S hS p y :=
  ((BigFppfOver.toScheme B S hS).map (p.map g)).appTop.hom

/-- The algebra structure given by restriction along `g`. Not an instance. -/
@[instance_reducible]
noncomputable def fibredSectionAlgebra {x y : 𝒳} (g : y ⟶ x) :
    Algebra (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y) :=
  (fibredSectionRestrict g).toAlgebra

/-- The sections of a module over `x`, as a module over the global functions on `x`. -/
@[instance_reducible]
noncomputable def fibredSectionsModule
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) (x : 𝒳) :
    Module (fibredSectionRing B S hS p x) (F.val.obj (op x)) :=
  inferInstanceAs (Module ((ringStructureSheafCore B S hS p hp B.topology le_rfl).obj.obj (op x))
    (F.val.obj (op x)))

/-- The sections over `y` as a module over the functions on `x`, through `g : y ⟶ x`. -/
@[instance_reducible]
noncomputable def fibredSectionsModuleOver
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) {x y : 𝒳}
    (g : y ⟶ x) : Module (fibredSectionRing B S hS p x) (F.val.obj (op y)) :=
  letI := fibredSectionsModule hp F y
  Module.compHom _ (fibredSectionRestrict g)

/-- Restriction of sections along `g`, as a linear map over the functions on `x`. -/
noncomputable def fibredSectionsRestrict
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) {x y : 𝒳}
    (g : y ⟶ x) :
    letI := fibredSectionsModule hp F x
    letI := fibredSectionsModuleOver hp F g
    F.val.obj (op x) →ₗ[fibredSectionRing B S hS p x] F.val.obj (op y) :=
  letI := fibredSectionsModule hp F x
  letI := fibredSectionsModuleOver hp F g
  { toFun := fun t => F.val.map g.op t
    map_add' := map_add (F.val.map g.op).hom
    map_smul' := fun c t => F.val.map_smul g.op c t }

/-- Restriction of sections along `g` is the restriction map of the presheaf of modules. -/
theorem fibredSectionsRestrict_apply
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) {x y : 𝒳}
    (g : y ⟶ x) (t : F.val.obj (op x)) : fibredSectionsRestrict hp F g t = F.val.map g.op t := rfl

/-- The base change comparison `𝒪(y) ⊗_{𝒪(x)} F(x) ⟶ F(y)` along `g : y ⟶ x`. -/
noncomputable def fibredSectionsBaseChange
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) {x y : 𝒳}
    (g : y ⟶ x) :
    letI := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
    letI := fibredSectionsModule hp F x
    letI := fibredSectionsModule hp F y
    TensorProduct (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
      (F.val.obj (op x)) →ₗ[
      fibredSectionRing B S hS p y] F.val.obj (op y) :=
  letI := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
  letI := fibredSectionsModule hp F x
  letI := fibredSectionsModule hp F y
  letI := fibredSectionsModuleOver hp F g
  haveI : IsScalarTower (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
      (F.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange _ (fibredSectionsRestrict hp F g)

/-- The base change comparison of the sections is the adjoint transpose
`Stacks.PresheafOfModules.restrictionBaseChange` of the restriction map. -/
theorem fibredSectionsBaseChange_eq_restrictionBaseChange
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) {x y : 𝒳}
    (g : y ⟶ x)
    (z : letI := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
      letI := fibredSectionsModule hp F x
      TensorProduct (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
        (F.val.obj (op x))) :
    fibredSectionsBaseChange hp F g z =
      restrictionBaseChange.{v, w, u, u} (R := fibredRings B S hS p) F.val g.op z := by
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
  let := fibredSectionsModule hp F x
  induction z using TensorProduct.inductionOn with
  | add a b ha hb =>
    exact ((map_add _ a b).trans (congrArg₂ (· + ·) ha hb)).trans (map_add _ a b).symm
  | tmul c t =>
    exact (restrictionBaseChange_tmul.{v, w, u, u} (R := fibredRings B S hS p) F.val g.op c t).symm

/-- A module on `𝒳` is *cartesian between affine objects* when every base change comparison
along a morphism between objects over affine schemes is bijective. -/
def IsCartesianBetweenAffines
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) : Prop :=
  ∀ ⦃x y : 𝒳⦄ (g : y ⟶ x), IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x) →
    IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y) →
      Function.Bijective (fibredSectionsBaseChange hp F g)

/-- **A quasi-coherent module on `𝒳` is cartesian between affine objects.** -/
theorem isCartesianBetweenAffines_of_isQuasicoherentOnSite
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : F.IsQuasicoherentOnSite) : IsCartesianBetweenAffines hp F := fun x y g hx hy => by
  have h := bijective_restrictionBaseChange_fibredRings_of_isQuasicoherentOnSite B S hS p hp F hF
    g hx hy
  rw [show (fibredSectionsBaseChange hp F g : _ → _) = _ from
    funext (fibredSectionsBaseChange_eq_restrictionBaseChange hp F g)]
  exact h

/-! ### Descent of spans along a finite fppf covering by affine objects -/

/-- The base change of the coordinate map `(κ → A) ⟶ (κ → B)` along `A → B` is surjective. -/
private theorem surjective_liftBaseChange_compLeft (A Bc : Type*) [CommRing A] [CommRing Bc]
    [Algebra A Bc] (κ : Type*) [Finite κ] :
    Function.Surjective (((Algebra.linearMap A Bc).compLeft κ).liftBaseChange Bc) := by
  classical
  have := Fintype.ofFinite κ
  refine (Module.BaseChange.bijective_liftBaseChange_of_basis
    (Pi.basisFun A κ) (Pi.basisFun Bc κ) ((Algebra.linearMap A Bc).compLeft κ)
    fun l => funext fun j => ?_).2
  change algebraMap A Bc (Pi.basisFun A κ l j) = Pi.basisFun Bc κ l j
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  by_cases h : j = l
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/-- A family whose span is the whole module has surjective linear combination map. -/
private theorem surjective_linearCombination_of_span_eq_top {R M ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [Fintype ι] {s : ι → M}
    (hs : Submodule.span R (Set.range s) = ⊤) :
    Function.Surjective (Fintype.linearCombination R s) := by
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
  exact hs

/-- **A section over an affine object lies in the span of a finite family of sections as soon as
its restriction to each member of a finite fppf covering family by affine objects lies in the
span of the restricted family.** -/
theorem mem_span_of_forall_restrict_mem_span_fibred
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) {x : 𝒳}
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    {n : ℕ} {z : Fin n → 𝒳} (φ : ∀ i, z i ⟶ x)
    (hz : ∀ i, IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (z i)))
    (hfppf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (z i)))
        (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φ i))) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    {κ : Type*} [Finite κ] (τ : κ → F.val.obj (op x)) {t : F.val.obj (op x)}
    (ht : ∀ i, letI := fibredSectionsModule hp F (z i)
      fibredSectionsRestrict hp F (φ i) t ∈ Submodule.span (fibredSectionRing B S hS p (z i))
        (Set.range fun l => fibredSectionsRestrict hp F (φ i) (τ l))) :
    letI := fibredSectionsModule hp F x
    t ∈ Submodule.span (fibredSectionRing B S hS p x) (Set.range τ) := by
  classical
  let := fibredSectionsModule hp F x
  let fκ : Fintype κ := Fintype.ofFinite κ
  let algI : ∀ i, Algebra (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p (z i)) :=
    fun i => fibredSectionAlgebra (φ i)
  let modZ : ∀ i, Module (fibredSectionRing B S hS p (z i)) (F.val.obj (op (z i))) :=
    fun i => fibredSectionsModule hp F (z i)
  let modI : ∀ i, Module (fibredSectionRing B S hS p x) (F.val.obj (op (z i))) :=
    fun i => fibredSectionsModuleOver hp F (φ i)
  have towI : ∀ i, IsScalarTower (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p (z i))
      (F.val.obj (op (z i))) := fun i => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have towP : ∀ i, IsScalarTower (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p (z i))
      (κ → fibredSectionRing B S hS p (z i)) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := hx
  have : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (z i))) := hz
  have hFF : Module.FaithfullyFlat (fibredSectionRing B S hS p x)
      (∀ i, fibredSectionRing B S hS p (z i)) :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage
      (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φ i))) hfppf (fun _ => rfl)
  let rP : ∀ i, (κ → fibredSectionRing B S hS p x) →ₗ[fibredSectionRing B S hS p x]
      (κ → fibredSectionRing B S hS p (z i)) := fun _ => (Algebra.linearMap _ _).compLeft κ
  let rN : ∀ i, F.val.obj (op x) →ₗ[fibredSectionRing B S hS p x] F.val.obj (op (z i)) :=
    fun i => fibredSectionsRestrict hp F (φ i)
  let bT := Fintype.linearCombination (fibredSectionRing B S hS p x) τ
  let bW : ∀ i, (κ → fibredSectionRing B S hS p (z i)) →ₗ[fibredSectionRing B S hS p (z i)]
      F.val.obj (op (z i)) := fun i => Fintype.linearCombination _ fun l => rN i (τ l)
  have hsq : ∀ (i) (q : κ → fibredSectionRing B S hS p x), rN i (bT q) = bW i (rP i q) := by
    intro i q
    change rN i (Fintype.linearCombination _ τ q) = Fintype.linearCombination _ _ (rP i q)
    rw [Fintype.linearCombination_apply, map_sum, Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun l _ => map_smul (rN i) (q l) (τ l)
  have hP : ∀ i,
      Function.Surjective ((rP i).liftBaseChange (fibredSectionRing B S hS p (z i))) :=
    fun _ => surjective_liftBaseChange_compLeft _ _ κ
  have hN : ∀ i, Function.Injective ((rN i).liftBaseChange (fibredSectionRing B S hS p (z i))) :=
    fun i => (hF (φ i) hx (hz i)).1
  have hn : ∀ i, rN i t ∈ LinearMap.range (bW i) := by
    intro i
    change rN i t ∈ LinearMap.range (Fintype.linearCombination _ fun l => rN i (τ l))
    rw [Fintype.range_linearCombination]
    exact ht i
  have hmem := Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
    (fibredSectionRing B S hS p x) (fun i => fibredSectionRing B S hS p (z i)) bT bW rP rN hsq hP
    hN hn
  rwa [show LinearMap.range bT =
    Submodule.span (fibredSectionRing B S hS p x) (Set.range τ) from
      Fintype.range_linearCombination _ _] at hmem

/-- **Finitely many sections over an affine object which generate the module locally span its
sections over that object.** -/
theorem span_eq_top_of_generates_fibred
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) {x : 𝒳}
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    {k : ℕ} (s : Fin k → F.val.obj (op x))
    (hs : PresheafOfModules.Generates (associatedTopology B S hS p B.topology) F.val s) :
    letI := fibredSectionsModule hp F x
    Submodule.span (fibredSectionRing B S hS p x) (Set.range s) = ⊤ := by
  let := fibredSectionsModule hp F x
  refine Submodule.eq_top_iff'.2 fun t => ?_
  obtain ⟨T, hT, hcomb⟩ := hs x (𝟙 x) t
  obtain ⟨n, z, φ, hzaff, hzT, -, hfppf⟩ :=
    FibredSite.exists_finite_affine_fppf_ofArrows_le B S hS p hp hx hT
  refine mem_span_of_forall_restrict_mem_span_fibred hp F hF hx φ hzaff hfppf s fun i => ?_
  let := fibredSectionsModule hp F (z i)
  obtain ⟨a, ha⟩ := hcomb (z i) (φ i) (hzT i)
  rw [Category.comp_id] at ha
  exact Submodule.mem_span_set'.2
    ⟨k, a, fun l => ⟨fibredSectionsRestrict hp F (φ i) (s l), ⟨l, rfl⟩⟩, ha⟩

/-- Finitely many locally generating sections over an affine object make its sections a finite
module. -/
theorem moduleFinite_sections_of_generates_fibred
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) {x : 𝒳}
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    {k : ℕ} (s : Fin k → F.val.obj (op x))
    (hs : PresheafOfModules.Generates (associatedTopology B S hS p B.topology) F.val s) :
    letI := fibredSectionsModule hp F x
    Module.Finite (fibredSectionRing B S hS p x) (F.val.obj (op x)) := by
  let := fibredSectionsModule hp F x
  exact Module.Finite.of_surjective _
    (surjective_linearCombination_of_span_eq_top (span_eq_top_of_generates_fibred hp F hF hx s hs))

/-- **The sections over an affine object of a module of finite type which is cartesian between
affine objects form a finite module.**  This is the fppf descent of finite generation. -/
theorem moduleFinite_sections_of_isFiniteTypeOnSite_fibred
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) (hft : F.IsFiniteTypeOnSite) {x : 𝒳}
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x)) :
    letI := fibredSectionsModule hp F x
    Module.Finite (fibredSectionRing B S hS p x) (F.val.obj (op x)) := by
  classical
  let := fibredSectionsModule hp F x
  obtain ⟨I, V, f, hcov, hgg⟩ := hft.locally_finitelyGenerated x
  obtain ⟨n, z, φ, hzaff, hzmem, -, hfppf⟩ :=
    FibredSite.exists_finite_affine_fppf_ofArrows_le B S hS p hp hx hcov
  let modZ : ∀ i, Module (fibredSectionRing B S hS p (z i)) (F.val.obj (op (z i))) :=
    fun i => fibredSectionsModule hp F (z i)
  have hfinz : ∀ i, ∃ (c : ℕ) (γ : Fin c → F.val.obj (op (z i))),
      Submodule.span (fibredSectionRing B S hS p (z i)) (Set.range γ) = ⊤ := by
    intro i
    obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff V f (φ i)).1 (hzmem i)
    obtain ⟨m, σ, hσ⟩ :=
      Stacks.SheafOfModules.exists_generates_of_hasFiniteGlobalGenerators_over F (V j) (hgg j)
    have hfin : Module.Finite (fibredSectionRing B S hS p (z i)) (F.val.obj (op (z i))) :=
      moduleFinite_sections_of_generates_fibred hp F hF (hzaff i) _
        (Stacks.SheafOfModules.generates_restrict b σ hσ)
    exact Module.Finite.exists_fin
  choose c γ hγ using hfinz
  have hdec : ∀ (i : Fin n) (l : Fin (c i)), ∃ (kk : ℕ)
      (t : Fin kk → fibredSectionRing B S hS p (z i)) (mm : Fin kk → F.val.obj (op x)),
      γ i l = ∑ q, t q • fibredSectionsRestrict hp F (φ i) (mm q) := by
    intro i l
    let algi : Algebra (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p (z i)) :=
      fibredSectionAlgebra (φ i)
    obtain ⟨ζ, hζ⟩ := (hF (φ i) hx (hzaff i)).2 (γ i l)
    obtain ⟨kk, t, mm, hmm⟩ := TensorProduct.exists_sum_tmul_eq ζ
    refine ⟨kk, t, mm, ?_⟩
    rw [← hζ, hmm, map_sum]
    rfl
  choose kk t mm hmm using hdec
  let τ : (Σ i : Fin n, Σ l : Fin (c i), Fin (kk i l)) → F.val.obj (op x) :=
    fun w => mm w.1 w.2.1 w.2.2
  have hspanz : ∀ i, Submodule.span (fibredSectionRing B S hS p (z i))
      (Set.range fun w => fibredSectionsRestrict hp F (φ i) (τ w)) = ⊤ := by
    intro i
    refine top_unique ?_
    rw [← hγ i]
    refine Submodule.span_le.2 ?_
    rintro y ⟨l, rfl⟩
    rw [hmm i l]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, l, q⟩, rfl⟩)
  have hsp : Submodule.span (fibredSectionRing B S hS p x) (Set.range τ) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun t' => ?_
    refine mem_span_of_forall_restrict_mem_span_fibred hp F hF hx φ hzaff hfppf τ fun i => ?_
    rw [hspanz i]
    exact Submodule.mem_top
  exact Module.Finite.of_surjective _ (surjective_linearCombination_of_span_eq_top hsp)

/-- Restriction of sections is functorial. -/
theorem fibredSectionsRestrict_comp
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    {x y w : 𝒳} (g : y ⟶ x) (e : w ⟶ y) (t : F.val.obj (op x)) :
    fibredSectionsRestrict hp F (e ≫ g) t =
      fibredSectionsRestrict hp F e (fibredSectionsRestrict hp F g t) :=
  F.val.map_comp_apply g.op e.op t

/-- Restriction of sections is semilinear over the restriction of functions. -/
theorem fibredSectionsRestrict_smul
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    {y w : 𝒳} (e : w ⟶ y) (a : fibredSectionRing B S hS p y) (t : F.val.obj (op y)) :
    letI := fibredSectionsModule hp F y
    letI := fibredSectionsModule hp F w
    fibredSectionsRestrict hp F e (a • t) =
      fibredSectionRestrict e a • fibredSectionsRestrict hp F e t :=
  F.val.map_smul e.op a t

/-- Restriction of global functions is functorial. -/
theorem fibredSectionRestrict_comp {x y w : 𝒳} (g : y ⟶ x) (e : w ⟶ y)
    (a : fibredSectionRing B S hS p x) :
    fibredSectionRestrict (e ≫ g) a = fibredSectionRestrict e (fibredSectionRestrict g a) := by
  change ((BigFppfOver.toScheme B S hS).map (p.map (e ≫ g))).appTop a = _
  rw [p.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-! ### A finite presentation of the sections over an affine object presents the module -/

/-- The base change of the coordinate map `(κ → A) ⟶ (κ → B)` along `A → B` is surjective. -/
theorem surjective_liftBaseChange_compLeft_algebraMap (A Bc : Type*) [CommRing A] [CommRing Bc]
    [Algebra A Bc] (κ : Type*) [Finite κ] :
    Function.Surjective (((Algebra.linearMap A Bc).compLeft κ).liftBaseChange Bc) :=
  surjective_liftBaseChange_compLeft A Bc κ

/-- **A module cartesian between affine objects whose sections over an affine object `z` are a
finitely presented module has a finite global presentation on the slice at `z`.**  Generators
and relations of the sections over `z` generate the module and its relations on the slice,
because over every affine object over `z` the sections are the base change of those over `z` and
the tensor product is right exact. -/
theorem hasFiniteGlobalPresentation_over_of_finitePresentation
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) {z : 𝒳}
    (hz : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (hfp : letI := fibredSectionsModule hp F z
      Module.FinitePresentation (fibredSectionRing B S hS p z) (F.val.obj (op z))) :
    (F.over z).HasFiniteGlobalPresentation := by
  classical
  let := fibredSectionsModule hp F z
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := fibredSectionRing B S hS p z)
    (M := F.val.obj (op z))
  let π := Fintype.linearCombination (fibredSectionRing B S hS p z) s
  have hπ : Function.Surjective π := surjective_linearCombination_of_span_eq_top hs
  have hK : (LinearMap.ker π).FG := Module.FinitePresentation.fg_ker π hπ
  obtain ⟨k, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hK
  have hrker : ∀ l, r l ∈ LinearMap.ker π := fun l => hr ▸ Submodule.subset_span ⟨l, rfl⟩
  -- the data over an affine object `y` over `z`
  have hloc : ∀ {y : 𝒳} (c : y ⟶ z), IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y) →
      (let := fibredSectionsModule hp F y;
        Submodule.span (fibredSectionRing B S hS p y)
          (Set.range fun i => fibredSectionsRestrict hp F c (s i)) = ⊤) ∧
      ∀ τ : Fin n → fibredSectionRing B S hS p y,
        (let := fibredSectionsModule hp F y;
          ∑ i, τ i • fibredSectionsRestrict hp F c (s i) = 0) →
        ∃ d : Fin k → fibredSectionRing B S hS p y, ∀ i,
          ∑ l, d l * fibredSectionRestrict c (r l i) = τ i := by
    intro y c hy
    let := fibredSectionsModule hp F y
    let alg := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) c
    let := fibredSectionsModuleOver hp F c
    have tw : IsScalarTower (fibredSectionRing B S hS p z) (fibredSectionRing B S hS p y)
        (F.val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hbc := hF c hz hy
    let rN := fibredSectionsRestrict hp F c
    let rP : (Fin n → fibredSectionRing B S hS p z) →ₗ[fibredSectionRing B S hS p z]
        (Fin n → fibredSectionRing B S hS p y) := (Algebra.linearMap _ _).compLeft (Fin n)
    let bW := Fintype.linearCombination (fibredSectionRing B S hS p y) fun i => rN (s i)
    have hsq : ∀ q, rN (π q) = bW (rP q) := by
      intro q
      change rN (Fintype.linearCombination _ s q) = Fintype.linearCombination _ _ (rP q)
      rw [Fintype.linearCombination_apply, map_sum, Fintype.linearCombination_apply]
      exact Finset.sum_congr rfl fun l _ => map_smul rN (q l) (s l)
    refine ⟨?_, fun τ hτ => ?_⟩
    · refine Submodule.eq_top_iff'.2 fun t => ?_
      obtain ⟨ζ, rfl⟩ := hbc.2 t
      induction ζ using TensorProduct.inductionOn with
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
      | tmul b m =>
        change b • rN m ∈ _
        refine Submodule.smul_mem _ b ?_
        obtain ⟨q, rfl⟩ := hπ m
        rw [hsq, ← Fintype.range_linearCombination]
        exact LinearMap.mem_range_self _ _
    · have hτ' : bW τ = 0 := by
        change Fintype.linearCombination _ _ τ = 0
        rw [Fintype.linearCombination_apply]
        exact hτ
      have hmem := Module.BaseChange.mem_span_image_ker_of_liftBaseChange π bW rP rN hsq
        (surjective_liftBaseChange_compLeft_algebraMap _ _ (Fin n)) hbc.1 hπ hτ'
      have hle : Submodule.span (fibredSectionRing B S hS p y)
          (rP '' (LinearMap.ker π : Set (Fin n → fibredSectionRing B S hS p z))) ≤
          Submodule.span (fibredSectionRing B S hS p y) (Set.range fun l => rP (r l)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨q, hq, rfl⟩
        rw [← hr] at hq
        induction hq using Submodule.span_induction with
        | mem q hq =>
          obtain ⟨l, rfl⟩ := hq
          exact Submodule.subset_span ⟨l, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
        | smul a q _ hq =>
          rw [map_smul, algebra_compatible_smul (fibredSectionRing B S hS p y) a]
          exact Submodule.smul_mem _ _ hq
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hle hmem)
      refine ⟨d, fun i => ?_⟩
      have := congrFun hd i
      rw [Finset.sum_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => rfl
  refine SheafOfModules.hasFiniteGlobalPresentation_over_of_generates F z s r (fun l => ?_)
    (fun V hV t => ?_) (fun V hV τ hτ => ?_)
  · have h := hrker l
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at h
    exact h
  · obtain ⟨I, y, φ, hyaff, hcov, -⟩ := FibredSite.exists_affine_fppf_ofArrows B S hS p hp V
    refine ⟨Sieve.ofArrows y φ, hcov, fun W g hg => ?_⟩
    obtain ⟨j, e, rfl⟩ := (Sieve.mem_ofArrows_iff y φ g).1 hg
    let := fibredSectionsModule hp F (y j)
    let := fibredSectionsModule hp F W
    have hspan := (hloc (φ j ≫ hV) (hyaff j)).1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hspan ▸ Submodule.mem_top : fibredSectionsRestrict hp F (φ j) t ∈ _)
    refine ⟨fun i => fibredSectionRestrict e (c i), ?_⟩
    change ∑ i, fibredSectionRestrict e (c i) • fibredSectionsRestrict hp F ((e ≫ φ j) ≫ hV) (s i) =
      fibredSectionsRestrict hp F (e ≫ φ j) t
    rw [fibredSectionsRestrict_comp hp F (φ j) e t, ← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fibredSectionsRestrict_smul hp F e, Category.assoc,
      fibredSectionsRestrict_comp hp F (φ j ≫ hV) e]
  · obtain ⟨I, y, φ, hyaff, hcov, -⟩ := FibredSite.exists_affine_fppf_ofArrows B S hS p hp V
    refine ⟨Sieve.ofArrows y φ, hcov, fun W g hg => ?_⟩
    obtain ⟨j, e, rfl⟩ := (Sieve.mem_ofArrows_iff y φ g).1 hg
    let := fibredSectionsModule hp F V
    let := fibredSectionsModule hp F (y j)
    let τ₀ : Fin n → fibredSectionRing B S hS p V := τ
    have hτV : ∑ i, τ₀ i • fibredSectionsRestrict hp F hV (s i) = 0 := hτ
    have hτ' : ∑ i, fibredSectionRestrict (φ j) (τ₀ i) •
        fibredSectionsRestrict hp F (φ j ≫ hV) (s i) = 0 := by
      have h0 := congrArg (fibredSectionsRestrict hp F (φ j)) hτV
      rw [map_sum, map_zero] at h0
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h0
      rw [fibredSectionsRestrict_smul hp F (φ j), fibredSectionsRestrict_comp hp F hV (φ j)]
    obtain ⟨d, hd⟩ := (hloc (φ j ≫ hV) (hyaff j)).2 _ hτ'
    refine ⟨fun l => fibredSectionRestrict e (d l), fun i => ?_⟩
    change ∑ l, fibredSectionRestrict e (d l) * fibredSectionRestrict ((e ≫ φ j) ≫ hV) (r l i) =
      fibredSectionRestrict (e ≫ φ j) (τ₀ i)
    rw [fibredSectionRestrict_comp (φ j) e, ← hd i, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Category.assoc, fibredSectionRestrict_comp (φ j ≫ hV) e]

end AlgebraicGeometry.Stack

end

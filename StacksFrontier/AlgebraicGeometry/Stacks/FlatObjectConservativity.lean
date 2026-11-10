module

public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf

/-!
# Restriction to the flat objects reflects isomorphisms of quasi-coherent modules

Let `𝒳` be an algebraic stack and `f : ℋ₁ ⟶ ℋ₂` a map of quasi-coherent `𝒪_𝒳`-modules on the
big fppf site of `𝒳`.  If `f` is bijective on sections over every *flat* object of `𝒳` — that is,
if the restriction `g⁻¹f` of `f` to the flat-fppf site of Stacks 0787 is an isomorphism — then `f`
is an isomorphism.

This is the input of the proof of Stacks 07B1 the source phrases as "a map of quasi-coherent
modules on `𝒳` whose restriction to any scheme smooth over `𝒳` is an isomorphism is an
isomorphism", and it is what makes the coherator of Stacks 0778 detectable on flat objects
(Stacks 0779, 0GQK).  The proof:

* over an object `x` lying over an affine scheme and admitting a morphism `x ⟶ y` to a flat
  object over an affine scheme, both modules are cartesian
  (`AlgebraicGeometry.Stack.isCartesianBetweenAffines_of_isQuasicoherentOnSite`), so `f` over `x`
  is the base change of `f` over `y`, which is bijective;
* such objects cover every object of `𝒳`: every object is covered by objects mapping to flat
  objects (`AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_inclusion`), a flat object is
  covered by flat objects over affine schemes
  (`AlgebraicGeometry.Stack.exists_isAffine_covering_of_object` and
  `AlgebraicGeometry.Stack.flatObject_of_flat`), and every object is covered by objects over affine
  schemes;
* injectivity of `f` and its local surjectivity are local, so `f` is a monomorphism and an
  epimorphism of sheaves of modules, hence an isomorphism.

## Main results

* `AlgebraicGeometry.Stack.bijective_app_of_isQuasicoherentOnSite_of_affine`: the affine step.
* `AlgebraicGeometry.Stack.goodPresieve_generate_mem`: the covering by good objects.
* `AlgebraicGeometry.Stack.isIso_of_isQuasicoherentOnSite_of_bijective_flat`: the
  conservativity.
* `AlgebraicGeometry.Stack.hom_ext_of_isQuasicoherentOnSite_of_flat`: restriction to the flat
  objects is faithful on maps out of a quasi-coherent module, whatever the target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

local notation "𝒪" => ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  B.topology le_rfl

local notation "𝐉" => associatedTopology B S hS 𝒳.val.val.p B.topology

/-- **The affine step.**  For a map of quasi-coherent modules and a morphism `φ : x ⟶ y` between
objects over affine schemes, bijectivity of `f` over `y` gives bijectivity over `x`: both modules
are cartesian, so `f` over `x` is the base change of `f` over `y`. -/
theorem bijective_app_of_isQuasicoherentOnSite_of_affine
    {H₁ H₂ : SheafOfModules.{u} 𝒪} (f : H₁ ⟶ H₂) (h₁ : H₁.IsQuasicoherentOnSite)
    (h₂ : H₂.IsQuasicoherentOnSite) {x y : 𝒳.val.val.obj} (φ : x ⟶ y)
    (hx : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hy : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y))
    (hf : Function.Bijective (f.val.app (op y))) :
    Function.Bijective (f.val.app (op x)) := by
  have hc₁ := isCartesianBetweenAffines_of_isQuasicoherentOnSite
    𝒳.val.isFiberedInGroupoids H₁ h₁ φ hy hx
  have hc₂ := isCartesianBetweenAffines_of_isQuasicoherentOnSite
    𝒳.val.isFiberedInGroupoids H₂ h₂ φ hy hx
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) φ
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids H₁ y
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids H₂ y
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids H₁ x
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids H₂ x
  -- `f` over `y`, as a linear equivalence over the functions on `y`
  let fy : H₁.val.obj (op y) →ₗ[fibredSectionRing B S hS 𝒳.val.val.p y] H₂.val.obj (op y) :=
    (f.val.app (op y)).hom
  let ey := LinearEquiv.ofBijective fy hf
  let T := LinearEquiv.lTensor (fibredSectionRing B S hS 𝒳.val.val.p x) ey
  -- the naturality square of the base change comparisons
  have hsq : ∀ z, f.val.app (op x) (fibredSectionsBaseChange 𝒳.val.isFiberedInGroupoids H₁ φ z) =
      fibredSectionsBaseChange 𝒳.val.isFiberedInGroupoids H₂ φ (T z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c t =>
      let a : H₁.val.obj (op x) := H₁.val.map φ.op t
      let b : H₂.val.obj (op x) := H₂.val.map φ.op (f.val.app (op y) t)
      have e₁ : fibredSectionsBaseChange 𝒳.val.isFiberedInGroupoids H₁ φ (c ⊗ₜ t) = c • a := rfl
      have e₂ : fibredSectionsBaseChange 𝒳.val.isFiberedInGroupoids H₂ φ (T (c ⊗ₜ t)) =
          c • b := rfl
      have hab : f.val.app (op x) a = b := PresheafOfModules.naturality_apply f.val φ.op t
      rw [e₁, e₂]
      exact ((f.val.app (op x)).hom.map_smul c a).trans (congrArg (c • ·) hab)
  refine ⟨fun s₁ s₂ h => ?_, fun t => ?_⟩
  · obtain ⟨z₁, rfl⟩ := hc₁.2 s₁
    obtain ⟨z₂, rfl⟩ := hc₁.2 s₂
    rw [hsq, hsq] at h
    exact congrArg _ (T.injective (hc₂.1 h))
  · obtain ⟨z, hz⟩ := hc₂.2 t
    obtain ⟨z', rfl⟩ := T.surjective z
    exact ⟨_, (hsq z').trans hz⟩

/-- The objects over which the affine step applies: arrows `w ⟶ W` whose source lies over an affine
scheme and admits a morphism to a flat object lying over an affine scheme. -/
def goodPresieve (W : 𝒳.val.val.obj) : Presieve W := fun w _ =>
  IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj w) ∧
    ∃ y : 𝒳.val.val.obj, flatObject B S hS 𝒳.val y ∧
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y) ∧ Nonempty (w ⟶ y)

/-- **Good objects cover every object.**  Every object is covered by objects admitting a morphism
to a flat object; a flat object is covered by flat objects over affine schemes; and every object
is covered by objects over affine schemes. -/
theorem goodPresieve_generate_mem (W : 𝒳.val.val.obj) :
    Sieve.generate (goodPresieve 𝒳 W) ∈ 𝐉 W := by
  refine GrothendieckTopology.transitive _
    (FlatFppf.hasLocalFactorizations_inclusion B S hS 𝒳 W) _ ?_
  rintro Y a ⟨d, ⟨φ⟩⟩
  obtain ⟨I, yi, fi, hcov, haff, hflat⟩ := exists_isAffine_covering_of_object B S hS 𝒳.val d.obj
  refine GrothendieckTopology.transitive _ ((𝐉).pullback_stable φ hcov) _ ?_
  intro Z b hb
  rw [Sieve.pullback_apply] at hb
  obtain ⟨Y', h, g, ⟨i⟩, hhg⟩ := hb
  obtain ⟨K, zk, gk, hcovZ, hzaff, -⟩ := exists_isAffine_covering_of_object B S hS 𝒳.val Z
  refine GrothendieckTopology.superset_covering _ ?_ hcovZ
  rintro V c hc
  obtain ⟨V', e, c', ⟨k⟩, rfl⟩ := hc
  rw [Sieve.pullback_apply, Sieve.pullback_apply]
  refine ⟨zk k, e, gk k ≫ b ≫ a,
    ⟨hzaff k, yi i, flatObject_of_flat B S hS 𝒳 (fi i) (hflat i) d.property, haff i,
      ⟨gk k ≫ h⟩⟩, ?_⟩
  simp only [Category.assoc]

/-- Two sections of a sheaf of modules over `W` are equal if their restrictions along every arrow
of `goodPresieve 𝒳 W` agree. -/
private theorem eq_of_map_eq_of_goodPresieve (T : SheafOfModules.{u} 𝒪) {W : 𝒳.val.val.obj}
    {t₁ t₂ : T.val.obj (op W)}
    (h : ∀ {w : 𝒳.val.val.obj} (g : w ⟶ W), goodPresieve 𝒳 W g →
      T.val.map g.op t₁ = T.val.map g.op t₂) : t₁ = t₂ :=
  ((Presieve.isSeparatedFor_iff_generate (R := goodPresieve 𝒳 W)).2
    (Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget T _
      (goodPresieve_generate_mem 𝒳 W)).isSeparatedFor).ext (fun _ g hg => h g hg)

/-- **Restriction to the flat objects reflects isomorphisms of quasi-coherent modules.**  A map of
quasi-coherent modules on the big fppf site of an algebraic stack which is bijective on sections
over every flat object is an isomorphism. -/
theorem isIso_of_isQuasicoherentOnSite_of_bijective_flat
    {H₁ H₂ : SheafOfModules.{u} 𝒪} (f : H₁ ⟶ H₂) (h₁ : H₁.IsQuasicoherentOnSite)
    (h₂ : H₂.IsQuasicoherentOnSite)
    (hf : ∀ y : 𝒳.val.val.obj, flatObject B S hS 𝒳.val y → Function.Bijective (f.val.app (op y))) :
    IsIso f := by
  have hgood : ∀ {W w : 𝒳.val.val.obj} (g : w ⟶ W), goodPresieve 𝒳 W g →
      Function.Bijective (f.val.app (op w)) := by
    rintro W w g ⟨hw, y, hy, hyaff, ⟨φ⟩⟩
    exact bijective_app_of_isQuasicoherentOnSite_of_affine 𝒳 f h₁ h₂ φ hw hyaff (hf y hy)
  have hinj : ∀ W : 𝒳.val.val.obj, Function.Injective (f.val.app (op W)) := by
    intro W s s' hss'
    refine eq_of_map_eq_of_goodPresieve 𝒳 H₁ fun g hg => (hgood g hg).1 ?_
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg _ hss'
  have hmono : Mono f :=
    (SheafOfModules.forget _).mono_of_mono_map
      (PresheafOfModules.mono_of_injective (f := f.val) fun {V} => hinj V.unop)
  have hepi : Epi f := by
    refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective f ⟨fun {W} t => ?_⟩
    refine GrothendieckTopology.superset_covering _ ?_ (goodPresieve_generate_mem 𝒳 W)
    rintro w g ⟨w', e, g', hg', rfl⟩
    obtain ⟨s, hs⟩ := (hgood g' hg').2 (H₂.val.map g'.op t)
    refine ⟨H₁.val.map e.op s, ?_⟩
    change f.val.app (op w) (H₁.val.map e.op s) = H₂.val.map (e ≫ g').op t
    rw [PresheafOfModules.naturality_apply]
    exact (congrArg (H₂.val.map e.op) hs).trans
      (PresheafOfModules.map_comp_apply H₂.val g'.op e.op t).symm
  exact isIso_of_mono_of_epi f

/-- **The affine step of faithfulness.**  Two maps out of a quasi-coherent module which agree over
a flat object `y` lying over an affine scheme agree over every object `x` lying over an affine
scheme and mapping to `y`: the sections over `x` are spanned over the functions on `x` by the
restrictions of the sections over `y`. -/
theorem app_eq_of_isQuasicoherentOnSite_of_affine
    {Z T : SheafOfModules.{u} 𝒪} (hZ : Z.IsQuasicoherentOnSite) (f₁ f₂ : Z ⟶ T)
    {x y : 𝒳.val.val.obj} (φ : x ⟶ y)
    (hx : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hy : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y))
    (h : f₁.val.app (op y) = f₂.val.app (op y)) :
    f₁.val.app (op x) = f₂.val.app (op x) := by
  have hc := isCartesianBetweenAffines_of_isQuasicoherentOnSite
    𝒳.val.isFiberedInGroupoids Z hZ φ hy hx
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) φ
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids Z y
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids Z x
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids T x
  ext s
  obtain ⟨z, rfl⟩ := hc.2 s
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c t =>
    let a : Z.val.obj (op x) := Z.val.map φ.op t
    have e : fibredSectionsBaseChange 𝒳.val.isFiberedInGroupoids Z φ (c ⊗ₜ t) = c • a := rfl
    have n₁ := PresheafOfModules.naturality_apply f₁.val φ.op t
    have n₂ := PresheafOfModules.naturality_apply f₂.val φ.op t
    rw [e]
    exact ((f₁.val.app (op x)).hom.map_smul c _).trans
      ((congrArg (c • ·) (n₁.trans (by rw [h]) |>.trans n₂.symm)).trans
        ((f₂.val.app (op x)).hom.map_smul c _).symm)

/-- **Restriction to the flat objects is faithful on maps out of a quasi-coherent module.**  Two
maps from a quasi-coherent module on the big fppf site of an algebraic stack to an arbitrary
module which agree over every flat object are equal.  The target need not be quasi-coherent: it
only has to be separated, and the source is spanned, over the good objects of
`AlgebraicGeometry.Stack.goodPresieve_generate_mem`, by restrictions of its sections over flat
objects. -/
theorem hom_ext_of_isQuasicoherentOnSite_of_flat
    {Z T : SheafOfModules.{u} 𝒪} (hZ : Z.IsQuasicoherentOnSite) {f₁ f₂ : Z ⟶ T}
    (h : ∀ y : 𝒳.val.val.obj, flatObject B S hS 𝒳.val y →
      f₁.val.app (op y) = f₂.val.app (op y)) :
    f₁ = f₂ := by
  have hgood : ∀ {W w : 𝒳.val.val.obj} (g : w ⟶ W), goodPresieve 𝒳 W g →
      f₁.val.app (op w) = f₂.val.app (op w) := by
    rintro W w g ⟨hw, y, hy, hyaff, ⟨φ⟩⟩
    exact app_eq_of_isQuasicoherentOnSite_of_affine 𝒳 hZ f₁ f₂ φ hw hyaff (h y hy)
  ext W s
  refine eq_of_map_eq_of_goodPresieve 𝒳 T fun g hg => ?_
  rw [← PresheafOfModules.naturality_apply f₁.val, ←
    PresheafOfModules.naturality_apply f₂.val, hgood g hg]

end AlgebraicGeometry.Stack

end

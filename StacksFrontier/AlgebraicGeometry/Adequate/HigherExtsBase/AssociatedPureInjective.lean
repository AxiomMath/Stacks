module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasicoherentChaotic
public import StacksFrontier.Algebra.Module.Pure.ExtAbelian
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCokernels
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedLocalizationAffineSections
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.MonoCriterion
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.PureExtComparison
public import StacksFrontier.RingTheory.Flat.CompleteDevissageStep

/-!
# Pure injective modules give injective adequate modules

Let `U = Spec A` be affine and `M ↦ M^a` the associated-module functor from `A`-modules to the
adequate `𝒪`-modules on a chosen big site over `U`. This module proves the three properties of
that functor which make a pure injective resolution `N ⟶ Iᐧ` into an injective resolution
`N^a ⟶ (Iᐧ)^a` in `Adeq(𝒪)`, as the proof of [Stacks, Tag 0709] asserts:

* it carries universally exact sequences to exact sequences of `Adeq(𝒪)`;
* it carries universally injective maps to monomorphisms, and conversely;
* it carries pure injective modules to injective objects of `Adeq(𝒪)`.

The third is [Stacks, Tag 0708] read through the equivalence of [Stacks, Tag 06ZJ]: the adequate
functors on the algebras of the site are the source's `𝒜`, and the injective objects of `𝒜` are
the extensions of pure injective modules.

## Main definitions

* `Stacks.Adequate.associatedAdequate` — `M ↦ M^a` as a functor into `Adeq(𝒪)`.

## Main results

* `Stacks.Adequate.universallyInjective_of_mono_moduleExtensionOn_map` — a map of modules whose
  extension to the algebras of the site is a monomorphism is universally injective.
* `Stacks.Adequate.exact_associatedAdequate_map` — universally exact sequences go to exact ones.
* `Stacks.Adequate.mono_associatedAdequate_map` — universally injective maps go to monomorphisms.
* `Stacks.Adequate.injective_associatedAdequate_obj` — `I^a` is injective in `Adeq(𝒪)` for a
  pure injective `I`.

## Implementation notes

All three are read off the affine-section functor `Φ : Adeq(𝒪) ⥤ Fun(Alg_A, Mod)` of the site,
which is fully faithful (`Stacks.Adequate.fullyFaithfulAffineSectionsFunctor`) and exact
(`Stacks.Adequate.preservesHomology_affineSections`), and which carries `M^a` to the module
extension `B ↦ B ⊗_A M` (`Stacks.Adequate.affineSectionsAssociatedTildeIso`). Exactness and
monomorphisms are then checked algebra by algebra, and the injectivity is the pushout argument of
`AdequateFunctor.injective_moduleExtension_of_pureInjective` carried out in `Adeq(𝒪)`.

A monomorphism of module extensions over the algebras of the site is universally injective
because the algebras of the site contain all algebras of finite type, and those detect the
kernel of a map of adequate functors (`Stacks.Adequate.BigSite.exists_preimage_of_siteAlgebras`);
so the extension over *all* algebras is a monomorphism, which is the criterion
`AdequateFunctor.universallyInjective_of_mono_moduleExtension_map`.

## References

* [Stacks Project, Tag 0708](https://stacks.math.columbia.edu/tag/0708)
* [Stacks Project, Tag 0709](https://stacks.math.columbia.edu/tag/0709)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-! ### Monomorphisms of module extensions on the algebras of the site -/

/-- **A monomorphism of module extensions on the algebras of the site comes from a universally
injective map of modules.** The algebras of the site contain all algebras of finite type, which
detect the kernel of a map of module extensions, so the extension to all algebras is a
monomorphism as well. -/
public theorem universallyInjective_of_mono_moduleExtensionOn_map {M N : ModuleCat.{u} A}
    (φ : M ⟶ N)
    (hφ : Mono ((AdequateFunctor.moduleExtensionFunctorOn.{u, u, u}
      (AdequateFunctor.siteAlgebraInclusion.{u, u} A (schemeSizeBelow B.cutoff))).map φ)) :
    UniversallyInjective φ.hom := by
  apply AdequateFunctor.universallyInjective_of_mono_moduleExtension_map.{u, u, u} φ
  apply PresheafOfModules.mono_of_injective
  intro R x y hxy
  obtain ⟨z, hz⟩ := BigSite.exists_preimage_of_siteAlgebras B
    (F := (0 : AdequateFunctor.ModuleValuedFunctor.{u, u} ↑A))
    (AdequateFunctor.isAdequate_moduleExtension M)
    (AdequateFunctor.isAdequate_moduleExtension N) 0
    ((AdequateFunctor.moduleExtensionFunctor.{u, u} (↑A)).map φ)
    (fun X w hw => ⟨0, by
      have hinj := PresheafOfModules.injective_of_mono
        ((AdequateFunctor.moduleExtensionFunctorOn.{u, u, u}
          (AdequateFunctor.siteAlgebraInclusion.{u, u} A (schemeSizeBelow B.cutoff))).map φ)
        (op (op X))
      exact (map_zero _).trans (hinj (hw.trans (map_zero _).symm)).symm⟩)
    R.unop.unop (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp (by rw [← hz]; simp)

/-- The extension of a universally injective map to the algebras of the site is a
monomorphism. -/
public theorem mono_moduleExtensionOn_map {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (hφ : UniversallyInjective φ.hom) :
    Mono ((AdequateFunctor.moduleExtensionFunctorOn.{u, u, u}
      (AdequateFunctor.siteAlgebraInclusion.{u, u} A (schemeSizeBelow B.cutoff))).map φ) := by
  have := AdequateFunctor.mono_moduleExtension_map_of_universallyInjective.{u, u, u} φ hφ
  apply PresheafOfModules.mono_of_injective
  intro X
  exact PresheafOfModules.injective_of_mono
    ((AdequateFunctor.moduleExtensionFunctor.{u, u} (↑A)).map φ) (op (op X.unop.unop.obj))

/-! ### The associated module as a functor into `Adeq(𝒪)` -/

/-- The associated module `M^a` of an `A`-module is adequate: it is the kernel of the zero map
`M^a ⟶ M^a`, a kernel presentation by associated quasi-coherent modules. -/
public theorem isAdequate_associatedTilde (M : ModuleCat.{u} A) :
    IsAdequate B ((associatedTilde B).obj M) :=
  isAdequate_of_isAssociatedKernel B _ (B.isAssociatedKernel_associatedModule (tilde M))

/-- **The associated-module functor `M ↦ M^a` into `Adeq(𝒪)`.** -/
public def associatedAdequate : ModuleCat.{u} A ⥤ (adequate.{u, u} B).FullSubcategory :=
  ObjectProperty.lift _ (associatedTilde B) (isAdequate_associatedTilde B)

/-- Composing `associatedAdequate B` with the inclusion of `Adeq(𝒪)` gives `associatedTilde B`. -/
public lemma associatedAdequate_comp_ι :
    associatedAdequate B ⋙ (adequate.{u, u} B).ι = associatedTilde B := rfl

/-- The inclusion of `Adeq(𝒪)` carries the map `f^a` of `Adeq(𝒪)` to the map `f^a` of
`Mod(𝒪)`. -/
public lemma ι_map_associatedAdequate {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (adequate.{u, u} B).ι.map ((associatedAdequate B).map f) = (associatedTilde B).map f :=
  ObjectProperty.ι_obj_lift_map _ _ _ f

/-- The functor `M ↦ M^a` into `Adeq(𝒪)` is additive. -/
public lemma additive_associatedAdequate : (associatedAdequate B).Additive := by
  have : (associatedTilde B).Additive := additive_associatedTilde B
  exact ⟨fun {_ _ _ _} => ObjectProperty.hom_ext _ (associatedTilde B).map_add⟩

/-- `M ↦ M^a` is fully faithful as a functor into `Adeq(𝒪)`. -/
public def fullyFaithfulAssociatedAdequate : (associatedAdequate B).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := (adequate.{u, u} B).ι)
    (fullyFaithfulAssociatedTilde B)

/-! ### Monomorphisms and exact sequences -/

section MonoConj

variable {C : Type*} [Category* C] {W X Y Z : C}

/-- A morphism conjugate to a monomorphism by isomorphisms is a monomorphism. Stated in an
abstract category so that the instance search it needs never runs in a category of
module-valued functors, where it does not terminate on universe constraints. -/
private lemma mono_of_mono_iso_comp (a : W ≅ X) (f : X ⟶ Y) (b : Y ≅ Z)
    (h : Mono (a.hom ≫ f ≫ b.hom)) : Mono f := by
  have hf : f = a.inv ≫ (a.hom ≫ f ≫ b.hom) ≫ b.inv := by simp
  rw [hf]
  infer_instance

/-- The conjugate of a monomorphism by isomorphisms is a monomorphism. -/
private lemma mono_iso_comp_of_mono (a : W ≅ X) (f : X ⟶ Y) (b : Y ≅ Z) (h : Mono f) :
    Mono (a.hom ≫ f ≫ b.hom) := by
  infer_instance

/-- The composite of a monomorphism with an isomorphism is a monomorphism. -/
private lemma mono_comp_iso_of_mono (f : W ⟶ X) (b : X ≅ Y) (h : Mono f) : Mono (f ≫ b.hom) := by
  infer_instance

/-- The composite of two monomorphisms is a monomorphism, with the instances passed
explicitly. -/
private lemma mono_comp_of_mono (f : W ⟶ X) (g : X ⟶ Y) (hf : Mono f) (hg : Mono g) :
    Mono (f ≫ g) :=
  mono_comp f g

/-- A naturality square with isomorphisms as horizontal maps, solved for the vertical map. -/
private lemma eq_iso_comp_of_comp_eq (a : W ≅ X) (f : W ⟶ Y) (g : X ⟶ Z) (b : Y ≅ Z)
    (h : f ≫ b.hom = a.hom ≫ g) : g = a.inv ≫ f ≫ b.hom := by
  rw [h, Iso.inv_hom_id_assoc]

end MonoConj

/-- The affine-section functor of the adequate modules, `Adeq(𝒪) ⥤ Fun(Alg_A, Mod)`. It is
fully faithful and exact. -/
abbrev adequateSections : (adequate.{u, u} B).FullSubcategory ⥤
    AdequateFunctor.ModuleValuedFunctorOn.{u}
      (AdequateFunctor.siteAlgebraInclusion.{u, u} A (schemeSizeBelow B.cutoff)) :=
  (adequate.{u, u} B).ι ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))

/-- `adequateSections` is faithful. -/
lemma faithful_adequateSections : (adequateSections B).Faithful :=
  have := (fullyFaithfulAffineSectionsFunctor.{u, u} B (A := A)).faithful
  Functor.Faithful.comp _ _

/-- `adequateSections` is fully faithful. -/
def fullyFaithfulAdequateSections : (adequateSections B).FullyFaithful :=
  (adequate.{u, u} B).fullyFaithfulι.comp (fullyFaithfulAffineSectionsFunctor.{u, u} B (A := A))

/-- Composing `associatedAdequate B` with `adequateSections B` gives the affine-section functor
of `associatedTilde B`. -/
lemma associatedAdequate_comp_adequateSections :
    associatedAdequate B ⋙ adequateSections B =
      associatedTilde B ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A)) :=
  (Functor.assoc _ _ _).symm.trans
    (congrArg (· ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))) (associatedAdequate_comp_ι B))

/-- **The affine-section functor of `M^a` is the module extension of `M`**, as a natural
isomorphism of functors into `Fun(Alg_A, Mod)` through `Adeq(𝒪)`. This is
`Stacks.Adequate.affineSectionsAssociatedTildeIso` transported along an equality of functors,
which keeps the crossing between the spellings `associatedTilde` and `associatedAdequate` at the
level of functors, the only level at which it is cheap. -/
def moduleExtensionOnIsoAdequateSections :
    AdequateFunctor.moduleExtensionFunctorOn.{u, u, u}
        (AdequateFunctor.siteAlgebraInclusion.{u, u} A (schemeSizeBelow B.cutoff)) ≅
      associatedAdequate B ⋙ adequateSections B :=
  affineSectionsAssociatedTildeIso B ≪≫ eqToIso (associatedAdequate_comp_adequateSections B).symm

/-- `adequateSections` on `f^a`, solved through the isomorphism with the module extension. -/
lemma adequateSections_map_associatedAdequate {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (adequateSections B).map ((associatedAdequate B).map f) =
      ((moduleExtensionOnIsoAdequateSections B).app M).symm.hom ≫
        (AdequateFunctor.moduleExtensionFunctorOn.{u, u, u}
          (AdequateFunctor.siteAlgebraInclusion.{u, u} A (schemeSizeBelow B.cutoff))).map f ≫
        ((moduleExtensionOnIsoAdequateSections B).app N).hom := by
  rw [← Functor.comp_map]
  exact eq_iso_comp_of_comp_eq ((moduleExtensionOnIsoAdequateSections B).app M) _ _
    ((moduleExtensionOnIsoAdequateSections B).app N)
    ((moduleExtensionOnIsoAdequateSections B).hom.naturality f)

/-- A morphism of `Adeq(𝒪)` is a monomorphism if its affine sections are. -/
private lemma mono_of_mono_adequateSections_map {P Q : (adequate.{u, u} B).FullSubcategory}
    (f : P ⟶ Q) (h : Mono ((adequateSections B).map f)) : Mono f :=
  have := faithful_adequateSections B
  (adequateSections B).mono_of_mono_map h

/-- **A map of modules whose associated map is a monomorphism of `Adeq(𝒪)` is universally
injective.** -/
public theorem universallyInjective_of_mono_associatedAdequate_map {M N : ModuleCat.{u} A}
    (φ : M ⟶ N) (hφ : Mono ((associatedAdequate B).map φ)) : UniversallyInjective φ.hom := by
  let := abelian_adequate B
  apply universallyInjective_of_mono_moduleExtensionOn_map B φ
  have hpl := preservesFiniteLimits_affineSections B
  have : PreservesLimitsOfShape WalkingCospan (adequateSections B) :=
    hpl.preservesFiniteLimits WalkingCospan
  have : (adequateSections B).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have h1 : Mono ((adequateSections B).map ((associatedAdequate B).map φ)) :=
    Functor.map_mono _ _
  rw [adequateSections_map_associatedAdequate] at h1
  exact mono_of_mono_iso_comp ((moduleExtensionOnIsoAdequateSections B).app M).symm _
    ((moduleExtensionOnIsoAdequateSections B).app N) h1

/-- **`M ↦ M^a` carries universally injective maps to monomorphisms of `Adeq(𝒪)`.** -/
public theorem mono_associatedAdequate_map {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (hφ : UniversallyInjective φ.hom) : Mono ((associatedAdequate B).map φ) := by
  have hm : Mono ((adequateSections B).map ((associatedAdequate B).map φ)) := by
    rw [adequateSections_map_associatedAdequate]
    exact mono_iso_comp_of_mono ((moduleExtensionOnIsoAdequateSections B).app M).symm _
      ((moduleExtensionOnIsoAdequateSections B).app N) (mono_moduleExtensionOn_map B φ hφ)
  exact mono_of_mono_adequateSections_map B _ hm

/-- **The extension to the algebras of the site carries universally exact sequences to exact
ones**: over each algebra `C` of the site the sequence is `C ⊗_A -` of a universally exact
sequence. -/
public theorem exact_moduleExtensionOn_map {X Y Z : ModuleCat.{u} A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : (AdequateFunctor.moduleExtensionFunctorOn.{u, u, u}
        (AdequateFunctor.siteAlgebraInclusion.{u, u} A (schemeSizeBelow B.cutoff))).map f ≫
      (AdequateFunctor.moduleExtensionFunctorOn.{u, u, u}
        (AdequateFunctor.siteAlgebraInclusion.{u, u} A (schemeSizeBelow B.cutoff))).map g = 0)
    (hQ : ∀ (Q : Type u) [AddCommGroup Q] [Module A Q],
      Function.Exact (f.hom.rTensor Q) (g.hom.rTensor Q)) :
    (ShortComplex.mk _ _ w).Exact := by
  apply ChaoticQCoh.exact_of_evaluation
  intro W
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact ((LinearMap.rTensor_exact_iff_lTensor_exact (Q := (W.unop.unop.obj : Type u))
    (f := f.hom) (g := g.hom)).1 (hQ _) x).1 hx

/-- **`M ↦ M^a` carries universally exact sequences to exact sequences of `Adeq(𝒪)`.** The
affine-section functor is faithful and exact on `Adeq(𝒪)` and carries the sequence to the module
extension of the sequence, which is exact over every algebra of the site. -/
public theorem exact_associatedAdequate_map {X Y Z : ModuleCat.{u} A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : (associatedAdequate B).map f ≫ (associatedAdequate B).map g = 0)
    (hfg : Function.Exact f.hom g.hom)
    (hQ : ∀ (Q : Type u) [AddCommGroup Q] [Module A Q],
      Function.Exact (f.hom.rTensor Q) (g.hom.rTensor Q)) :
    letI := abelian_adequate B
    (ShortComplex.mk _ _ w).Exact := by
  let := abelian_adequate B
  have := preservesFiniteLimits_affineSections B
  have := preservesFiniteColimits_affineSections B
  have := faithful_adequateSections B
  have := additive_associatedAdequate B
  have hfg0 : f ≫ g = 0 := ModuleCat.hom_ext hfg.linearMap_comp_eq_zero
  let S0 : ShortComplex (ModuleCat.{u} A) := ShortComplex.mk f g hfg0
  show (S0.map (associatedAdequate B)).Exact
  rw [← ShortComplex.exact_map_iff_of_faithful _ (adequateSections B), ← ShortComplex.map_comp]
  exact (ShortComplex.exact_iff_of_iso (S0.mapNatIso (moduleExtensionOnIsoAdequateSections B))).1
    (exact_moduleExtensionOn_map B f g _ hQ)

/-! ### Injectivity -/

/-- **Every adequate `𝒪`-module embeds into an associated module.** Its affine-section functor is
adequate ([Stacks, Tag 06VI]), so it embeds into a module extension `C ↦ C ⊗_A M`, which is the
affine-section functor of `M^a`; and the affine-section functor is fully faithful. -/
public theorem exists_mono_associatedAdequate (P : (adequate.{u, u} B).FullSubcategory) :
    ∃ (M : ModuleCat.{u} A) (m : P ⟶ (associatedAdequate B).obj M), Mono m := by
  have hP := isAdequate_affineSectionFunctor.{u, u} B P.obj P.property A (𝟙 (Spec A)) B.base_mem
  obtain ⟨M, i, hi⟩ := AdequateFunctor.exists_mono_to_moduleExtension_on.{u, u, u} hP
  let i' : (adequateSections B).obj P ⟶ (adequateSections B).obj ((associatedAdequate B).obj M) :=
    i ≫ ((moduleExtensionOnIsoAdequateSections B).app M).hom
  have hi' : Mono i' := mono_comp_iso_of_mono _ ((moduleExtensionOnIsoAdequateSections B).app M) hi
  refine ⟨M, (fullyFaithfulAdequateSections B).preimage i', ?_⟩
  apply mono_of_mono_adequateSections_map B
  rwa [Functor.FullyFaithful.map_preimage]

/-- **[Stacks, Tag 0708] in `Adeq(𝒪)`: the associated module of a pure injective module is an
injective object of `Adeq(𝒪)`.** Given a monomorphism `F ⟶ G` of adequate modules and a map
`F ⟶ I^a`, form the pushout `P` in `Adeq(𝒪)`; then `I^a ⟶ P` is a monomorphism, `P` embeds into
some `M^a`, and the composite `I^a ⟶ M^a` is the associated map of a universally injective
`I ⟶ M`, which pure injectivity of `I` splits. The splitting retracts `P` onto `I^a`. -/
public theorem injective_associatedAdequate_obj (I : ModuleCat.{u} A)
    (hI : Module.PureInjective A I) : Injective ((associatedAdequate B).obj I) := by
  let := abelian_adequate B
  refine Injective.mk ?_
  intro F G g f hf
  let P : (adequate.{u, u} B).FullSubcategory := pushout f g
  let j : (associatedAdequate B).obj I ⟶ P := pushout.inr f g
  have hj : Mono j := Abelian.mono_pushout_of_mono_f f g
  obtain ⟨M, m, hm⟩ := exists_mono_associatedAdequate B P
  let k : (associatedAdequate B).obj I ⟶ (associatedAdequate B).obj M := j ≫ m
  have hk : Mono k := mono_comp_of_mono _ _ hj hm
  let φ : I ⟶ M := (fullyFaithfulAssociatedAdequate B).preimage k
  have hkφ : (associatedAdequate B).map φ = k := (fullyFaithfulAssociatedAdequate B).map_preimage k
  have hφ : UniversallyInjective φ.hom :=
    universallyInjective_of_mono_associatedAdequate_map B φ (hkφ ▸ hk)
  obtain ⟨r, hr⟩ := (hI I M _ φ.hom (LinearMap.range φ.hom).mkQ
    (Module.injective_of_universallyInjective.{u, u} φ.hom hφ) (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm hφ).2.1 (LinearMap.id : I →ₗ[A] I)
  have hr' : φ ≫ ModuleCat.ofHom r = 𝟙 I := ModuleCat.hom_ext hr
  let s : P ⟶ (associatedAdequate B).obj I := m ≫ (associatedAdequate B).map (ModuleCat.ofHom r)
  have hsplit : j ≫ s = 𝟙 _ := by
    show j ≫ (m ≫ _) = _
    rw [← Category.assoc]
    show k ≫ _ = _
    rw [← hkφ, ← Functor.map_comp, hr']
    exact (associatedAdequate B).map_id I
  refine ⟨pushout.inl f g ≫ s, ?_⟩
  rw [← Category.assoc, pushout.condition, Category.assoc, hsplit, Category.comp_id]

/-! ### Pure extensions as extensions of adequate modules -/

/-- **`Pext^n_A(M, N) = Ext^n_{Adeq(𝒪)}(M^a, N^a)` for every `n`**, the computation in the proof of
[Stacks, Tag 0709] which identifies the adequate modules over `Spec A` with the adequate functors
of [Stacks, Tag 06ZJ] and their injective resolutions with the pure injective resolutions of
[Stacks, Tag 0708]. A pure injective resolution `N ⟶ Iᐧ` gives the injective resolution
`N^a ⟶ (Iᐧ)^a` of `Adeq(𝒪)`, and the class of a cocycle `f : M → Iⁿ` goes to the class of the
cocycle `f^a`; see `Module.pureExtAddEquivExt`, whose naturality in `M` and `N` is
`Module.pureExtAddEquivExt_naturality_left` and `Module.pureExtAddEquivExt_naturality_right`. -/
public def pureExtAddEquivExtAdequate (M N : ModuleCat.{u} A) (n : ℕ) :
    letI := abelian_adequate B
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    Module.pureExt (A := A) M N n ≃+
      Abelian.Ext ((associatedAdequate B).obj M) ((associatedAdequate B).obj N) n :=
  letI := abelian_adequate B
  letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
    HasDerivedCategory.standard _
  letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
    hasExt_of_hasDerivedCategory _
  haveI := additive_associatedAdequate B
  Module.pureExtAddEquivExt (associatedAdequate B) (injective_associatedAdequate_obj B)
    (fun φ hφ => mono_associatedAdequate_map B φ hφ)
    (fun f g w hfg hQ => exact_associatedAdequate_map B f g w hfg hQ)
    (fullyFaithfulAssociatedAdequate B) M N n

end Stacks.Adequate

end

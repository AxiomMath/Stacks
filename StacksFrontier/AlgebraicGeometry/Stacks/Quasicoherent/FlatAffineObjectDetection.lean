module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionMapTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations

/-!
# Maps of quasi-coherent modules are detected on flat affine objects

Let `𝒳` be an algebraic stack and `φ : 𝓕 ⟶ 𝓖` a map in `QCoh(𝒪_𝒳)`.  Every object of `𝒳` is
covered, for the fppf topology, by objects lying over affine schemes which admit a morphism to a
*flat* object lying over an affine scheme: by the atlas every object is covered by objects
mapping to a flat object (`AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_inclusion`),
and a flat object is covered by flat objects over affine schemes.  Over a morphism `z ⟶ w` of
objects over affine schemes the map `φ_z` is the base change of `φ_w`
(`AlgebraicGeometry.FibredSite.bijective_app_of_hom`).  Hence:

* if `φ` is bijective on the sections at every flat object over an affine scheme, `φ` is an
  isomorphism;
* if `φ` is surjective on the sections at every flat object over an affine scheme, `φ` is
  locally surjective, hence an epimorphism.

## Main definitions

* `AlgebraicGeometry.Stack.flatAffineFactorSieve`: the sieve of arrows into an object whose
  source admits a morphism to a flat object over an affine scheme.

## Main results

* `AlgebraicGeometry.Stack.flatAffineFactorSieve_mem`: that sieve covers.
* `AlgebraicGeometry.Stack.generate_affine_flatAffineFactorSieve_mem`: so do its members with
  affine source.
* `AlgebraicGeometry.Stack.isIso_of_bijective_app_flatObject`: a map of quasi-coherent modules
  which is bijective on sections at every flat object over an affine scheme is an isomorphism.
* `AlgebraicGeometry.Stack.isLocallySurjective_of_surjective_app_flatObject`: a map of
  quasi-coherent modules which is surjective on sections at every flat object over an affine
  scheme is locally surjective.

## References

* [Stacks Project, Tag 0GQF](https://stacks.math.columbia.edu/tag/0GQF)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
-/

@[expose] public section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- A flat object is covered by flat objects over affine schemes, along morphisms with flat
underlying morphism of schemes. -/
theorem exists_affine_flatObject_covering {w : 𝒳.val.val.obj}
    (hw : flatObject B S hS 𝒳.val w) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳.val.val.obj) (φ : ∀ j, y j ⟶ w),
      (∀ j, IsAffineOver B S hS (𝒳.val.val.p.obj (y j))) ∧
      (∀ j, flatObject B S hS 𝒳.val (y j)) ∧
      (∀ j, Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (φ j)))) ∧
      (∀ t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj w),
        ∃ j, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (φ j)))) ∧
      Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf w := by
  obtain ⟨I, y, φ, haff, hcov, hfppf⟩ :=
    FibredSite.exists_affine_fppf_ofArrows B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids w
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfppf
  exact ⟨I, y, φ, haff, fun j => flatObject_of_flat B S hS 𝒳 (φ j) (hfppf.2 j).1 hw,
    fun j => (hfppf.2 j).1, hfppf.1, hcov⟩

/-- The sieve of arrows into `x` whose source admits a morphism to a flat object lying over an
affine scheme. -/
def flatAffineFactorSieve (x : 𝒳.val.val.obj) : Sieve x where
  arrows z _ := ∃ w : 𝒳.val.val.obj, flatObject B S hS 𝒳.val w ∧
    IsAffineOver B S hS (𝒳.val.val.p.obj w) ∧ Nonempty (z ⟶ w)
  downward_closed := by
    rintro _ _ _ ⟨w, hw, hwa, ⟨g⟩⟩ e
    exact ⟨w, hw, hwa, ⟨e ≫ g⟩⟩

/-- **Every object is covered by objects mapping to a flat object over an affine scheme.** -/
theorem flatAffineFactorSieve_mem (x : 𝒳.val.val.obj) :
    flatAffineFactorSieve B S hS 𝒳 x ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x := by
  let J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf
  refine J.transitive (FlatFppf.hasLocalFactorizations_inclusion.{u, w} B S hS 𝒳 x) _ ?_
  rintro z f ⟨d, ⟨ψ⟩⟩
  obtain ⟨I, y, φ, haff, hflat, -, -, hcov⟩ := exists_affine_flatObject_covering B S hS 𝒳 d.property
  refine J.superset_covering ?_ (J.pullback_stable ψ hcov)
  rintro _ _ ⟨_, e, _, ⟨j⟩, _⟩
  exact ⟨y j, hflat j, haff j, ⟨e⟩⟩

/-- **The members with affine source of `flatAffineFactorSieve` generate a covering sieve.** -/
theorem generate_affine_flatAffineFactorSieve_mem (x : 𝒳.val.val.obj) :
    Sieve.generate ((flatAffineFactorSieve B S hS 𝒳 x).restrictToObjects
        fun z => IsAffineOver B S hS (𝒳.val.val.p.obj z)) ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x :=
  GrothendieckTopology.generate_restrictToObjects_mem _ _
    (fun X => by
      obtain ⟨I, y, φ, haff, hcov, -⟩ :=
        FibredSite.exists_affine_fppf_ofArrows B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids X
      exact ⟨I, y, φ, haff, hcov⟩)
    _ (flatAffineFactorSieve_mem B S hS 𝒳 x)

variable {B S hS 𝒳}

/-- The members of `flatAffineFactorSieve` with affine source. -/
abbrev affineFlatAffineFactorArrows (x : 𝒳.val.val.obj) : Presieve x :=
  (flatAffineFactorSieve B S hS 𝒳 x).restrictToObjects
    fun z => IsAffineOver B S hS (𝒳.val.val.p.obj z)

section Sections

/-- A sieve containing all members of `affineFlatAffineFactorArrows x` is covering. -/
private theorem mem_associatedTopology_of_affineFlatAffineFactorArrows {x : 𝒳.val.val.obj}
    {R : Sieve x} (h : ∀ ⦃z⦄ (f : z ⟶ x), affineFlatAffineFactorArrows x f → R f) :
    R ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x :=
  GrothendieckTopology.superset_covering _
    (by rw [Sieve.generate_le_iff]; exact fun z f hf => h f hf)
    (generate_affine_flatAffineFactorSieve_mem B S hS 𝒳 x)

variable {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
  𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G)

/-- If `φ` is bijective on sections at flat objects over affine schemes, it is bijective on
sections at every member of `affineFlatAffineFactorArrows`. -/
theorem bijective_app_of_mem_affineFlatAffineFactorArrows
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Bijective (φ.hom.val.app (op w)))
    {x z : 𝒳.val.val.obj} {f : z ⟶ x} (hf : affineFlatAffineFactorArrows x f) :
    Function.Bijective (φ.hom.val.app (op z)) := by
  obtain ⟨⟨w, hw, hwa, ⟨g⟩⟩, hz⟩ := hf
  exact FibredSite.bijective_app_of_hom F.property G.property φ.hom g hwa hz (h w hw hwa)

/-- If `φ` is surjective on sections at flat objects over affine schemes, it is surjective on
sections at every member of `affineFlatAffineFactorArrows`. -/
theorem surjective_app_of_mem_affineFlatAffineFactorArrows
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Surjective (φ.hom.val.app (op w)))
    {x z : 𝒳.val.val.obj} {f : z ⟶ x} (hf : affineFlatAffineFactorArrows x f) :
    Function.Surjective (φ.hom.val.app (op z)) := by
  obtain ⟨⟨w, hw, hwa, ⟨g⟩⟩, hz⟩ := hf
  exact FibredSite.surjective_app_of_hom F.property G.property φ.hom g hwa hz (h w hw hwa)

/-- **A map of quasi-coherent modules surjective at flat affine objects is locally
surjective.** -/
theorem isLocallySurjective_of_surjective_app_flatObject
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Surjective (φ.hom.val.app (op w))) :
    Presheaf.IsLocallySurjective (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      ((PresheafOfModules.toPresheaf _).map φ.hom.val) := by
  refine ⟨fun {x} s => mem_associatedTopology_of_affineFlatAffineFactorArrows fun z f hf => ?_⟩
  exact surjective_app_of_mem_affineFlatAffineFactorArrows φ h hf (G.obj.val.map f.op s)

/-- **A map of quasi-coherent modules bijective at flat affine objects is locally
injective.** -/
theorem isLocallyInjective_of_bijective_app_flatObject
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Bijective (φ.hom.val.app (op w))) :
    Presheaf.IsLocallyInjective (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      ((PresheafOfModules.toPresheaf _).map φ.hom.val) := by
  refine ⟨fun {x} a b hab =>
    mem_associatedTopology_of_affineFlatAffineFactorArrows fun z f hf => ?_⟩
  apply (bijective_app_of_mem_affineFlatAffineFactorArrows φ h hf).1
  have ha := PresheafOfModules.naturality_apply φ.hom.val f.op a
  have hb := PresheafOfModules.naturality_apply φ.hom.val f.op b
  have hab' : φ.hom.val.app x a = φ.hom.val.app x b := hab
  exact ha.trans (hab' ▸ hb.symm)

/-- **A map of quasi-coherent modules bijective at flat affine objects is bijective at every
object.** -/
theorem bijective_app_of_bijective_app_flatObject
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Bijective (φ.hom.val.app (op w))) (x : 𝒳.val.val.objᵒᵖ) :
    Function.Bijective (φ.hom.val.app x) := by
  let T := (SheafOfModules.toSheaf _).map φ.hom
  have : IsIso T := (Sheaf.isLocallyBijective_iff_isIso T).1
    ⟨isLocallyInjective_of_bijective_app_flatObject φ h,
      isLocallySurjective_of_surjective_app_flatObject φ fun w hw hwa => (h w hw hwa).2⟩
  exact (ConcreteCategory.isIso_iff_bijective (T.hom.app x)).1
    (NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map T) x)

/-- **Stacks 0GQF, the step "a map of `QCoh(𝒪_𝒳)` is an isomorphism as soon as it is one at the
flat objects".**  A map of quasi-coherent modules on an algebraic stack which is bijective on
sections at every flat object lying over an affine scheme is an isomorphism. -/
theorem isIso_of_bijective_app_flatObject
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Bijective (φ.hom.val.app (op w))) : IsIso φ := by
  have h1 : IsIso ((PresheafOfModules.toPresheaf _).map φ.hom.val) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro x
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_app_of_bijective_app_flatObject φ h x)
  have h2 : IsIso φ.hom.val := isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  have h3 : IsIso φ.hom := by
    have : IsIso ((SheafOfModules.forget _).map φ.hom) := h2
    exact isIso_of_reflects_iso _ (SheafOfModules.forget _)
  have : IsIso ((ObjectProperty.ι _).map φ) := h3
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map φ

/-- **A map of quasi-coherent modules on an algebraic stack which is bijective on sections at
every flat object is an isomorphism.** -/
theorem isIso_of_bijective_app_flatObject'
    (h : ∀ w, flatObject B S hS 𝒳.val w → Function.Bijective (φ.hom.val.app (op w))) :
    IsIso φ :=
  isIso_of_bijective_app_flatObject φ fun w hw _ => h w hw

end Sections

end AlgebraicGeometry.Stack

end

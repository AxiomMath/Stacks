module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Topology.Sheaves.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Left exactness of the internal hom of `O_X`-modules

For a ringed space `(X, O_X)`, with `O_X` a sheaf of commutative rings `Rc`, this file
characterizes the internal hom `SheafHom_{O_X}(F, G)` of two `O_X`-modules and proves that it is
left exact in each variable.

## Main definitions

* `structureSheaf`: the sheaf of rings underlying a sheaf of commutative rings.
* `SheafHom`: an `O_X`-module whose sections over each open `U` are identified with
  `Hom_{O_U}(F|_U, G|_U)`, compatibly with restrictions and with the `O_X`-module structure.
* `SheafHom.IsPrecomp`, `SheafHom.IsPostcomp`: a morphism between internal homs acts on sections
  by precomposition, resp. postcomposition, with a given morphism.

## Main results

* `sheafHom_exact_of_sectionwise`: a sequence `0 ⟶ M ⟶ N ⟶ P` of `O_X`-modules is exact if it is
  exact on sections over every open.
* `sheafHom_leftExact_fst`: if `F₂ ⟶ F₁ ⟶ F ⟶ 0` is exact, then
  `0 ⟶ SheafHom(F, G) ⟶ SheafHom(F₁, G) ⟶ SheafHom(F₂, G)` is exact.
* `sheafHom_leftExact_snd`: if `0 ⟶ G ⟶ G₁ ⟶ G₂` is exact, then
  `0 ⟶ SheafHom(F, G) ⟶ SheafHom(F, G₁) ⟶ SheafHom(F, G₂)` is exact.

## References

* [Stacks, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ZeroObject

universe v u

variable {X : TopCat.{v}}

/-- The underlying sheaf of (not-necessarily-commutative) rings of a sheaf of
commutative rings `Rc`, obtained by forgetting commutativity. -/
@[ega "0 4.1.1"]
noncomputable abbrev structureSheaf (Rc : TopCat.Sheaf CommRingCat.{v} X) :
    TopCat.Sheaf RingCat.{v} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj Rc

/-! ### Scalar actions on sections of `O_X`-modules

The section rings of `structureSheaf Rc`, of `Rc` itself and of their restrictions to the slice
site `Over U` are the same rings written in different ways; the instances below transport the
module structures on sections between them. -/

/-- Sections of the restriction `M|_U` over an object `W` of the slice site `Over U` form a module
over the sections of `R` on `W.left`: the structure sheaf of the slice site is the pushforward of
`R` along `Over.forget U`, so the two scalar rings are the same ring. -/
noncomputable instance moduleSliceSections {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}} {M : SheafOfModules.{v} R} {U : C}
    {W : (Over U)ᵒᵖ} : Module (R.obj.obj (op W.unop.left)) ((M.over U).val.obj W) :=
  inferInstanceAs (Module ((R.over U).obj.obj W) ((M.over U).val.obj W))

/-- `moduleSliceSections` for a slice object presented as `Over.mk f`. -/
noncomputable instance moduleSliceSectionsMk {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}} {M : SheafOfModules.{v} R} {U V : C}
    {f : V ⟶ U} : Module (R.obj.obj (op V)) ((M.over U).val.obj (op (Over.mk f))) :=
  inferInstanceAs (Module ((R.over U).obj.obj (op (Over.mk f))) _)

/-- Sections over `U` of a sheaf of modules over a sheaf of rings obtained by forgetting
commutativity form a module over the commutative section ring `Rc.obj.obj U`, which is the same
ring as the `RingCat`-valued one. -/
noncomputable instance moduleCommSections {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    {Rc : Sheaf J CommRingCat.{v}}
    {M : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat.{v} RingCat.{v})).obj Rc)}
    {U : Cᵒᵖ} : Module (Rc.obj.obj U) (M.val.obj U) :=
  inferInstanceAs
    (Module (((sheafCompose J (forget₂ CommRingCat.{v} RingCat.{v})).obj Rc).obj.obj U) _)

/-- `moduleCommSections` for the structure sheaf of a topological space. -/
noncomputable instance moduleCommSectionsTop {Rc : TopCat.Sheaf CommRingCat.{v} X}
    {M : SheafOfModules.{v} (structureSheaf Rc)} {U : (Opens X)ᵒᵖ} :
    Module (Rc.obj.obj U) (M.val.obj U) :=
  inferInstanceAs (Module ((structureSheaf Rc).obj.obj U) (M.val.obj U))

/-- Sections of `M|_U` over an object `W` of the slice site form a module over the sections of the
slice-site *commutative* structure sheaf `Rc.over U` at `W`. -/
noncomputable instance moduleCommSliceSheafSections {Rc : TopCat.Sheaf CommRingCat.{v} X}
    {M : SheafOfModules.{v} (structureSheaf Rc)} {U : Opens X} {W : (Over U)ᵒᵖ} :
    Module ((Rc.over U).obj.obj W) ((M.over U).val.obj W) :=
  inferInstanceAs (Module (((structureSheaf Rc).over U).obj.obj W) ((M.over U).val.obj W))

/-- `moduleCommSliceSheafSections` for a slice object presented as `Over.mk f`. -/
noncomputable instance moduleCommSliceSectionsMk {Rc : TopCat.Sheaf CommRingCat.{v} X}
    {M : SheafOfModules.{v} (structureSheaf Rc)} {U V : Opens X} {f : V ⟶ U} :
    Module (Rc.obj.obj (op V)) ((M.over U).val.obj (op (Over.mk f))) :=
  inferInstanceAs (Module (((structureSheaf Rc).over U).obj.obj (op (Over.mk f))) _)

/-- The slice-site structure sheaf at the terminal object `Over.mk (𝟙 U)` of `Over U` acts on the
plain sections over `U`: both are the section ring of `Rc` on `U`. -/
noncomputable instance moduleSliceUnitSections {Rc : TopCat.Sheaf CommRingCat.{v} X}
    {M : SheafOfModules.{v} (structureSheaf Rc)} {U : Opens X} :
    Module ((Rc.over U).obj.obj (op (Over.mk (𝟙 U)))) (M.val.obj (op U)) :=
  inferInstanceAs (Module ((structureSheaf Rc).obj.obj (op U)) _)

/-- Restriction of scalars does not change the underlying module, so the action of the *target*
ring survives it. -/
noncomputable instance moduleRestrictScalarsTarget {R S : RingCat.{v}} {f : R ⟶ S}
    {N : ModuleCat.{v} S} : Module S ((ModuleCat.restrictScalars (RingCat.Hom.hom f)).obj N) :=
  inferInstanceAs (Module S N)

/-- `moduleRestrictScalarsTarget` with the scalar ring in the commutative spelling. -/
noncomputable instance moduleRestrictScalarsTargetComm {Rc : TopCat.Sheaf CommRingCat.{v} X}
    {U V : (Opens X)ᵒᵖ} {f : (structureSheaf Rc).obj.obj U ⟶ (structureSheaf Rc).obj.obj V}
    {N : ModuleCat.{v} ((structureSheaf Rc).obj.obj V)} :
    Module (Rc.obj.obj V) ((ModuleCat.restrictScalars (RingCat.Hom.hom f)).obj N) :=
  inferInstanceAs (Module ((structureSheaf Rc).obj.obj V) N)

/-- The identity ring maps of the two spellings of a section ring compose to the identity. -/
instance ringHomCompTripleStructureSheaf {Rc : TopCat.Sheaf CommRingCat.{v} X}
    {U : (Opens X)ᵒᵖ} :
    RingHomCompTriple (RingHom.id ((structureSheaf Rc).obj.obj U)) (RingHom.id (Rc.obj.obj U))
      (RingHom.id (Rc.obj.obj U)) :=
  ⟨rfl⟩

/-- `ringHomCompTripleStructureSheaf` on the slice site: the identity ring maps of the two
spellings of a slice-site section ring compose to the identity. -/
instance ringHomCompTripleSliceForget {Rc : TopCat.Sheaf CommRingCat.{v} X} {U : Opens X}
    {V : (Over U)ᵒᵖ} :
    RingHomCompTriple (RingHom.id (((structureSheaf Rc).over U).obj.obj V))
      (RingHom.id (((sheafCompose ((Opens.grothendieckTopology (X : Type v)).over U)
        (forget₂ CommRingCat.{v} RingCat.{v})).obj (Rc.over U)).obj.obj V))
      (RingHom.id (((sheafCompose ((Opens.grothendieckTopology (X : Type v)).over U)
        (forget₂ CommRingCat.{v} RingCat.{v})).obj (Rc.over U)).obj.obj V)) :=
  ⟨rfl⟩

/-- `ringHomCompTripleSliceForget` in the other order. -/
instance ringHomCompTripleSliceForget' {Rc : TopCat.Sheaf CommRingCat.{v} X} {U : Opens X}
    {V : (Over U)ᵒᵖ} :
    RingHomCompTriple
      (RingHom.id (((sheafCompose ((Opens.grothendieckTopology (X : Type v)).over U)
        (forget₂ CommRingCat.{v} RingCat.{v})).obj (Rc.over U)).obj.obj V))
      (RingHom.id (((structureSheaf Rc).over U).obj.obj V))
      (RingHom.id (((structureSheaf Rc).over U).obj.obj V)) :=
  ⟨rfl⟩

/-- Sections of the restriction `M|_U` over an object `W` of the slice site form a module over the
commutative section ring of `Rc` on `W.left`. -/
noncomputable instance moduleCommSliceSections {Rc : TopCat.Sheaf CommRingCat.{v} X}
    {M : SheafOfModules.{v} (structureSheaf Rc)} {U : Opens X} {W : (Over U)ᵒᵖ} :
    Module (Rc.obj.obj (op W.unop.left)) ((M.over U).val.obj W) :=
  inferInstanceAs (Module (((structureSheaf Rc).over U).obj.obj W) ((M.over U).val.obj W))

variable (Rc : TopCat.Sheaf CommRingCat.{v} X)

/-- `SheafHom Rc F G` packages the internal hom `SheafHom_{O_X}(F, G)` of two
`O_X`-modules `F`, `G`: an honest `O_X`-module `obj`, an additive identification of
its sections over each open `U` with `Hom_{O_U}(F|_U, G|_U) = (F.over U ⟶ G.over U)`,
together with two naturality axioms making the identification respect the obvious
restriction maps (`restrict_natural`) and the `O_X`-module structure (`smul_natural`).

The component of a morphism `m : F.over U ⟶ G.over U` at an open `W ≤ U` is the
module map `m.val.app (op (Over.mk (homOfLE hWU))) : F.val.obj (op W) ⟶ G.val.obj (op W)`
(definitionally, since the site of `R.over U` is the over-category `Over U`). -/
@[sga "4 IV 12.2"]
structure SheafHom (F G : SheafOfModules.{v} (structureSheaf Rc)) where
  /-- The internal hom as an honest object of `SheafOfModules R`. -/
  obj : SheafOfModules.{v} (structureSheaf Rc)
  /-- Sections of `obj` over `U` are `Hom_{O_U}(F|_U, G|_U)` (additive identification). -/
  sectionsEquiv : ∀ U : Opens X, (obj.val.obj (op U)) ≃+ (F.over U ⟶ G.over U)
  /-- Naturality with restriction maps: restricting a section of `obj` from `U` to
  `V ≤ U` corresponds to restricting the associated `O_U`-module homomorphism, read
  off componentwise at every `W ≤ V`. -/
  restrict_natural : ∀ {U V : Opens X} (hVU : V ≤ U) (s : obj.val.obj (op U))
      {W : Opens X} (hWV : W ≤ V) (x : F.val.obj (op W)),
      (sectionsEquiv U s).val.app (op (Over.mk (homOfLE (le_trans hWV hVU)))) x =
        (sectionsEquiv V (obj.val.map (homOfLE hVU).op s)).val.app
          (op (Over.mk (homOfLE hWV))) x
  /-- Compatibility with the `O_X`-module structure: the action of `r ∈ O_X(U)` on a
  section corresponds, on each component `W ≤ U`, to scalar multiplication by `r|_W`
  on `G(W)`. -/
  smul_natural : ∀ (U : Opens X) (r : (structureSheaf Rc).obj.obj (op U))
      (s : obj.val.obj (op U)) {W : Opens X} (hWU : W ≤ U) (x : F.val.obj (op W)),
      (sectionsEquiv U (r • s)).val.app (op (Over.mk (homOfLE hWU))) x =
        ((structureSheaf Rc).obj.map (homOfLE hWU).op r) •
          ((sectionsEquiv U s).val.app (op (Over.mk (homOfLE hWU))) x)

namespace SheafHom

/-- A morphism `m : H.obj ⟶ H'.obj` of `O_X`-modules is the precomposition map
`β*` induced by `β : F₁ ⟶ F` (contravariant functoriality in the first argument) iff,
under the section identifications, it acts on sections over every open `U` by
precomposition with `β|_U`. -/
def IsPrecomp {F₁ F G : SheafOfModules.{v} (structureSheaf Rc)} (β : F₁ ⟶ F)
    (H : SheafHom Rc F G) (H' : SheafHom Rc F₁ G) (m : H.obj ⟶ H'.obj) : Prop :=
  ∀ (U : Opens X) (s : H.obj.val.obj (op U)),
    H'.sectionsEquiv U (m.val.app (op U) s) = (β.over U) ≫ (H.sectionsEquiv U s)

/-- A morphism `m : H.obj ⟶ H'.obj` of `O_X`-modules is the postcomposition map
`u_*` induced by `u : G ⟶ G₁` (covariant functoriality in the second argument) iff,
under the section identifications, it acts on sections over every open `U` by
postcomposition with `u|_U`. -/
def IsPostcomp {F G G₁ : SheafOfModules.{v} (structureSheaf Rc)} (u : G ⟶ G₁)
    (H : SheafHom Rc F G) (H' : SheafHom Rc F G₁) (m : H.obj ⟶ H'.obj) : Prop :=
  ∀ (U : Opens X) (s : H.obj.val.obj (op U)),
    H'.sectionsEquiv U (m.val.app (op U) s) = (H.sectionsEquiv U s) ≫ (u.over U)

end SheafHom

/-- Let `M --f--> N --g--> P` be morphisms of `O_X`-modules with `f ≫ g = 0`. If for every open
`U` the map `f(U)` on sections is a monomorphism and `M(U) --f(U)--> N(U) --g(U)--> P(U)` is
exact, then `0 ⟶ M ⟶ N ⟶ P` is exact. -/
theorem sheafHom_exact_of_sectionwise
    (M N P : SheafOfModules.{v} (structureSheaf Rc)) (f : M ⟶ N) (g : N ⟶ P)
    (hfg : f ≫ g = 0)
    (hmono : ∀ U : (Opens X)ᵒᵖ,
      Mono ((SheafOfModules.evaluation (structureSheaf Rc) U).map f))
    (hmid : ∀ U : (Opens X)ᵒᵖ,
      (ShortComplex.mk ((SheafOfModules.evaluation (structureSheaf Rc) U).map f)
        ((SheafOfModules.evaluation (structureSheaf Rc) U).map g)
        (by
          have : (SheafOfModules.evaluation (structureSheaf Rc) U).PreservesZeroMorphisms :=
            Functor.preservesZeroMorphisms_of_preserves_terminal_object
          rw [← Functor.map_comp, hfg, Functor.map_zero])).Exact) :
    (ComposableArrows.mk₃
      (0 : (0 : SheafOfModules.{v} (structureSheaf Rc)) ⟶ M) f g).Exact := by
  have hJRI : JointlyReflectIsomorphisms (fun (U : (Opens X)ᵒᵖ) =>
      SheafOfModules.evaluation (structureSheaf Rc) U) := by
    refine JointlyReflectIsomorphisms.mk (fun {A B} φ hφ => ?_)
    have happ : ∀ U, IsIso (((PresheafOfModules.toPresheaf (structureSheaf Rc).obj).map
        ((SheafOfModules.forget (structureSheaf Rc)).map φ)).app U) := by
      intro U
      have : IsIso ((SheafOfModules.evaluation (structureSheaf Rc) U).map φ) := hφ U
      exact (inferInstance : IsIso ((forget₂ (ModuleCat _) Ab).map
        ((SheafOfModules.evaluation (structureSheaf Rc) U).map φ)))
    have : IsIso ((PresheafOfModules.toPresheaf (structureSheaf Rc).obj).map
        ((SheafOfModules.forget (structureSheaf Rc)).map φ)) := NatIso.isIso_of_isIso_app _
    have : IsIso ((SheafOfModules.forget (structureSheaf Rc)).map φ) :=
      isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf (structureSheaf Rc).obj)
    exact isIso_of_reflects_iso _ (SheafOfModules.forget (structureSheaf Rc))
  have hMf : Mono f := by have := hmono; exact hJRI.mono f
  have hIC : (ComposableArrows.mk₃
      (0 : (0 : SheafOfModules.{v} (structureSheaf Rc)) ⟶ M) f g).IsComplex := by
    refine ComposableArrows.IsComplex.mk (fun i hi => ?_)
    have hi' : i ≤ 1 := by omega
    interval_cases i
    · simp
    · simpa [ComposableArrows.map', ComposableArrows.mk₃, ComposableArrows.mk₂,
        ComposableArrows.mk₁, ComposableArrows.Precomp.map] using hfg
  refine ComposableArrows.Exact.mk hIC (fun i hi => ?_)
  have hi' : i ≤ 1 := by omega
  interval_cases i
  · rw [ShortComplex.exact_iff_mono]
    · exact hMf
    · simp
  · have hSCexact : (ShortComplex.mk f g hfg).Exact := by
      set φ : M ⟶ kernel g := kernel.lift g f hfg with hφ
      have hφι : φ ≫ kernel.ι g = f := kernel.lift_ι g f hfg
      have hiso : ∀ U : (Opens X)ᵒᵖ,
          IsIso ((SheafOfModules.evaluation (structureSheaf Rc) U).map φ) := by
        intro U
        set G := SheafOfModules.evaluation (structureSheaf Rc) U with hG
        set a := G.map φ with ha0
        set kι := G.map (kernel.ι g) with hkι
        have hakι : a ≫ kι = G.map f := by rw [ha0, hkι, ← Functor.map_comp, hφι]
        have hPZU : G.PreservesZeroMorphisms :=
          Functor.preservesZeroMorphisms_of_preserves_terminal_object
        have : G.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape G
        have hkιmono : Mono kι := by
          have : Mono (kernel.ι g) := inferInstance
          exact G.map_mono (kernel.ι g)
        have hfinj : Function.Injective (ConcreteCategory.hom (G.map f)) := by
          rw [← ModuleCat.mono_iff_injective]; exact hmono U
        have hkιinj : Function.Injective (ConcreteCategory.hom kι) := by
          rw [← ModuleCat.mono_iff_injective]; exact hkιmono
        have hexact := (ShortComplex.moduleCat_exact_iff _).mp (hmid U)
        rw [ConcreteCategory.isIso_iff_bijective]
        refine ⟨?_, ?_⟩
        · intro x x' hxx'
          apply hfinj
          rw [← hakι, ModuleCat.comp_apply, ModuleCat.comp_apply, hxx']
        · intro y
          have hzero : (ConcreteCategory.hom (G.map g)) ((ConcreteCategory.hom kι) y) = 0 := by
            have hcomp : kι ≫ G.map g = 0 := by
              rw [hkι, ← Functor.map_comp, kernel.condition g]; simp
            rw [← ModuleCat.comp_apply, hcomp]; simp
          obtain ⟨x, hx⟩ := hexact ((ConcreteCategory.hom kι) y) hzero
          refine ⟨x, ?_⟩
          apply hkιinj
          rw [← ModuleCat.comp_apply, hakι, hx]
      have : IsIso φ := hJRI.isIso φ
      have hexk : (ShortComplex.mk (kernel.ι g) g (kernel.condition g)).Exact :=
        ShortComplex.exact_kernel g
      refine ShortComplex.exact_of_iso ?_ hexk
      symm
      refine ShortComplex.isoMk (asIso φ) (Iso.refl _) (Iso.refl _) ?_ ?_
      · change φ ≫ kernel.ι g = f ≫ 𝟙 _
        rw [hφι, Category.comp_id]
      · change g ≫ 𝟙 _ = 𝟙 _ ≫ g
        rw [Category.comp_id, Category.id_comp]
    exact hSCexact

/-- Restriction to the slice site over `U` preserves the vanishing of a composite. -/
private theorem over_comp_eq_zero {A B C : SheafOfModules.{v} (structureSheaf Rc)} (f : A ⟶ B)
    (g : B ⟶ C) (h : f ≫ g = 0) (U : Opens X) : f.over U ≫ g.over U = 0 := by
  have : PreservesFiniteColimits (SheafOfModules.overFunctor (structureSheaf Rc) U) := by
    unfold SheafOfModules.overFunctor; infer_instance
  have : (SheafOfModules.overFunctor (structureSheaf Rc) U).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object
  rw [← Functor.map_comp, h, Functor.map_zero]

/-- Restriction to the slice site over `U` preserves monomorphisms. -/
private theorem mono_over {A B : SheafOfModules.{v} (structureSheaf Rc)} (f : A ⟶ B) [Mono f]
    (U : Opens X) : Mono (f.over U) := by
  have : PreservesFiniteLimits (SheafOfModules.overFunctor (structureSheaf Rc) U) := by
    unfold SheafOfModules.overFunctor; infer_instance
  exact (SheafOfModules.overFunctor (structureSheaf Rc) U).map_mono f

/-- Restriction to the slice site over `U` preserves epimorphisms. -/
private theorem epi_over {A B : SheafOfModules.{v} (structureSheaf Rc)} (f : A ⟶ B) [Epi f]
    (U : Opens X) : Epi (f.over U) := by
  have : PreservesFiniteColimits (SheafOfModules.overFunctor (structureSheaf Rc) U) := by
    unfold SheafOfModules.overFunctor; infer_instance
  exact (SheafOfModules.overFunctor (structureSheaf Rc) U).map_epi f

set_option maxHeartbeats 1000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- Left exactness of `SheafHom` in the first argument. Given an exact sequence
`F₂ --α--> F₁ --β--> F → 0` of `O_X`-modules (encoded as the exact `ComposableArrows`
`F₂ → F₁ → F → 0`, whose final node forces `β` epi), and internal homs `SheafHom(F,G)`,
`SheafHom(F₁,G)`, `SheafHom(F₂,G)` with induced precomposition maps `β* = mβ`, `α* = mα`
(morphisms of `O_X`-modules), the induced sequence of `O_X`-modules
  `0 → SheafHom(F, G) --β*--> SheafHom(F₁, G) --α*--> SheafHom(F₂, G)`
is exact in `SheafOfModules R` (`β*` is mono and `im β* = ker α*`). -/
@[stacks 01CO "(1)",
  ega "0 4.1.5" "special case",
  ega "0 6.7.6" "partial",
  sga "4 IV 12.2" "partial"]
theorem sheafHom_leftExact_fst
    (F₂ F₁ F G : SheafOfModules.{v} (structureSheaf Rc)) (α : F₂ ⟶ F₁) (β : F₁ ⟶ F)
    (hin : (ComposableArrows.mk₃ α β (0 : F ⟶ 0)).Exact)
    (HF : SheafHom Rc F G) (HF₁ : SheafHom Rc F₁ G) (HF₂ : SheafHom Rc F₂ G)
    (mβ : HF.obj ⟶ HF₁.obj) (mα : HF₁.obj ⟶ HF₂.obj)
    (hmβ : SheafHom.IsPrecomp Rc β HF HF₁ mβ) (hmα : SheafHom.IsPrecomp Rc α HF₁ HF₂ mα) :
    (ComposableArrows.mk₃
      (0 : (0 : SheafOfModules.{v} (structureSheaf Rc)) ⟶ HF.obj) mβ mα).Exact := by
  have : Epi β := (hin.exact 1).epi_f (by rfl)
  refine sheafHom_exact_of_sectionwise Rc HF.obj HF₁.obj HF₂.obj mβ mα ?hfg ?hmono ?hmid
  case hfg =>
    ext U s
    apply (HF₂.sectionsEquiv U.unop).injective
    change HF₂.sectionsEquiv U.unop (mα.val.app U (mβ.val.app U s)) = HF₂.sectionsEquiv U.unop 0
    rw [hmα U.unop (mβ.val.app U s), hmβ U.unop s, map_zero, ← Category.assoc,
      over_comp_eq_zero Rc α β (hin.toIsComplex.zero 0), zero_comp]
  case hmono =>
    intro U
    have := epi_over Rc β U.unop
    rw [ModuleCat.mono_iff_injective]
    intro s t hst
    apply (HF.sectionsEquiv U.unop).injective
    apply (cancel_epi (β.over U.unop)).mp
    rw [← hmβ U.unop s, ← hmβ U.unop t]
    exact congrArg (HF₁.sectionsEquiv U.unop) hst
  case hmid =>
    intro U
    have factor : ∀ (φ : F₁.over U.unop ⟶ G.over U.unop), α.over U.unop ≫ φ = 0 →
        ∃ ψ : F.over U.unop ⟶ G.over U.unop, β.over U.unop ≫ ψ = φ := by
      have hαβ : α ≫ β = 0 := hin.toIsComplex.zero 0
      have hSexact : (ShortComplex.mk α β hαβ).Exact := hin.exact 0
      have : PreservesFiniteColimits (SheafOfModules.overFunctor (structureSheaf Rc) U.unop) := by
        unfold SheafOfModules.overFunctor; infer_instance
      have : (SheafOfModules.overFunctor (structureSheaf Rc) U.unop).PreservesZeroMorphisms :=
        Functor.preservesZeroMorphisms_of_preserves_initial_object
      have hcfork := CokernelCofork.mapIsColimit _ hSexact.gIsCokernel
        (SheafOfModules.overFunctor (structureSheaf Rc) U.unop)
      exact fun φ hφ => ⟨_, (CokernelCofork.IsColimit.desc' hcfork φ hφ).2⟩
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    set φ := HF₁.sectionsEquiv U.unop x₂ with hφdef
    have hαφ : α.over U.unop ≫ φ = 0 := by
      rw [hφdef, ← hmα U.unop x₂, show mα.val.app (op U.unop) x₂ = 0 from hx₂, map_zero]
    obtain ⟨ψ, hψ⟩ := factor φ hαφ
    refine ⟨(HF.sectionsEquiv U.unop).symm ψ, ?_⟩
    apply (HF₁.sectionsEquiv U.unop).injective
    change HF₁.sectionsEquiv U.unop (mβ.val.app (op U.unop) ((HF.sectionsEquiv U.unop).symm ψ))
      = HF₁.sectionsEquiv U.unop x₂
    rw [hmβ U.unop ((HF.sectionsEquiv U.unop).symm ψ), AddEquiv.apply_symm_apply, hψ, hφdef]

set_option maxHeartbeats 1000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- Left exactness of `SheafHom` in the second argument. Given an exact sequence
`0 → G --u--> G₁ --v--> G₂` of `O_X`-modules (encoded as the exact `ComposableArrows`
`0 → G → G₁ → G₂`, whose first node forces `u` mono), and internal homs `SheafHom(F,G)`,
`SheafHom(F,G₁)`, `SheafHom(F,G₂)` with induced postcomposition maps `u_* = mu`, `v_* = mv`
(morphisms of `O_X`-modules), the induced sequence of `O_X`-modules
  `0 → SheafHom(F, G) --u_*--> SheafHom(F, G₁) --v_*--> SheafHom(F, G₂)`
is exact in `SheafOfModules R` (`u_*` is mono and `im u_* = ker v_*`). -/
@[stacks 01CO "(2)",
  ega "0 4.1.5" "special case",
  sga "4 IV 12.2" "partial",
  sga "4 V 6.0" "6.0, special case"]
theorem sheafHom_leftExact_snd
    (F G G₁ G₂ : SheafOfModules.{v} (structureSheaf Rc)) (u : G ⟶ G₁) (v : G₁ ⟶ G₂)
    (hin : (ComposableArrows.mk₃
      (0 : (0 : SheafOfModules.{v} (structureSheaf Rc)) ⟶ G) u v).Exact)
    (HG : SheafHom Rc F G) (HG₁ : SheafHom Rc F G₁) (HG₂ : SheafHom Rc F G₂)
    (mu : HG.obj ⟶ HG₁.obj) (mv : HG₁.obj ⟶ HG₂.obj)
    (hmu : SheafHom.IsPostcomp Rc u HG HG₁ mu) (hmv : SheafHom.IsPostcomp Rc v HG₁ HG₂ mv) :
    (ComposableArrows.mk₃
      (0 : (0 : SheafOfModules.{v} (structureSheaf Rc)) ⟶ HG.obj) mu mv).Exact := by
  have : Mono u := hin.exact 0 |>.mono_g (by rfl)
  refine sheafHom_exact_of_sectionwise Rc HG.obj HG₁.obj HG₂.obj mu mv ?hfg ?hmono ?hmid
  case hfg =>
    ext U s
    apply (HG₂.sectionsEquiv U.unop).injective
    change HG₂.sectionsEquiv U.unop (mv.val.app U (mu.val.app U s)) = HG₂.sectionsEquiv U.unop 0
    rw [hmv U.unop (mu.val.app U s), hmu U.unop s, map_zero, Category.assoc,
      over_comp_eq_zero Rc u v (hin.toIsComplex.zero 1), comp_zero]
  case hmono =>
    intro U
    have := mono_over Rc u U.unop
    rw [ModuleCat.mono_iff_injective]
    intro s t hst
    apply (HG.sectionsEquiv U.unop).injective
    apply (cancel_mono (u.over U.unop)).mp
    rw [← hmu U.unop s, ← hmu U.unop t]
    exact congrArg (HG₁.sectionsEquiv U.unop) hst
  case hmid =>
    intro U
    have factor : ∀ (φ : F.over U.unop ⟶ G₁.over U.unop), φ ≫ v.over U.unop = 0 →
        ∃ ψ : F.over U.unop ⟶ G.over U.unop, ψ ≫ u.over U.unop = φ := by
      have huv : u ≫ v = 0 := hin.toIsComplex.zero 1
      have hSexact : (ShortComplex.mk u v huv).Exact := hin.exact 1
      have : PreservesFiniteLimits (SheafOfModules.overFunctor (structureSheaf Rc) U.unop) := by
        unfold SheafOfModules.overFunctor; infer_instance
      have : (SheafOfModules.overFunctor (structureSheaf Rc) U.unop).PreservesZeroMorphisms :=
        Functor.preservesZeroMorphisms_of_preserves_terminal_object
      have hfork := KernelFork.mapIsLimit _ hSexact.fIsKernel
        (SheafOfModules.overFunctor (structureSheaf Rc) U.unop)
      exact fun φ hφ => ⟨_, (KernelFork.IsLimit.lift' hfork φ hφ).2⟩
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    set φ := HG₁.sectionsEquiv U.unop x₂ with hφdef
    have hvφ : φ ≫ v.over U.unop = 0 := by
      rw [hφdef, ← hmv U.unop x₂, show mv.val.app (op U.unop) x₂ = 0 from hx₂, map_zero]
    obtain ⟨ψ, hψ⟩ := factor φ hvφ
    refine ⟨(HG.sectionsEquiv U.unop).symm ψ, ?_⟩
    apply (HG₁.sectionsEquiv U.unop).injective
    change HG₁.sectionsEquiv U.unop (mu.val.app (op U.unop) ((HG.sectionsEquiv U.unop).symm ψ))
      = HG₁.sectionsEquiv U.unop x₂
    rw [hmu U.unop ((HG.sectionsEquiv U.unop).symm ψ), AddEquiv.apply_symm_apply, hψ, hφdef]


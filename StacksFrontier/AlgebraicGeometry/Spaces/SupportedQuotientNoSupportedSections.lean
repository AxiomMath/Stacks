module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient by the sections supported on a closed subset has no supported sections

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `T` be a
**closed** subset of its points and let `F` be an `𝒪_X`-module.  The sections of `F` supported on
`T` form a submodule `AlgebraicGeometry.Space.supportedSectionsSubmodule` (Stacks 0859); this
file proves that the quotient `F/Γ_T(F)` has no nonzero local section supported on `T`.

This is the space-level counterpart of the scheme-level
`AlgebraicGeometry.Scheme.Modules.supportedSections_compl_cokernel_eq_zero`, and it is the last
hypothesis of `AlgebraicGeometry.Space.exists_supportedQuotientIso` — the `hQ` input of
`AlgebraicGeometry.Space.exists_strictTransformSheafIso` — that
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformUniversalProperty.lean` records as not
established.

## Main results

* `AlgebraicGeometry.Space.sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen`: for `T`
  closed, a section of `F` over a chart `W` which restricts to zero on every subchart whose
  points lie over `Tᶜ` is supported on `T`.  This is the maximality of the open zero locus of
  Stacks 04KA.
* `AlgebraicGeometry.Space.exists_factorisation_smallEtalePostcomp`: a chart of `X` whose
  structure morphism factors through an étale `j : V ⟶ X` is, up to a morphism of charts which
  is the identity on the underlying object, the image under
  `AlgebraicGeometry.Space.smallEtalePostcomp` of a chart of `V`.
* `AlgebraicGeometry.Space.kernelSectionsSupportedIn_etaleModulePullbackAdjunction_unit`: the
  unit `F ⟶ j_*(F|_V)` of Stacks 03LU kills only sections supported on `T`, when `V` carries
  every point outside `T`.
* `AlgebraicGeometry.Space.supportedSectionsSubmodule_ι_eq_zero`: the inclusion of the
  submodule of Stacks 0859 at the empty set of points is the zero morphism.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_pushforwardModules` and
  `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_modulePushforward`: a direct image along a
  morphism no point of whose source lies over `T` has no sections supported on `T`.  This is
  Stacks 085B at a morphism with empty preimage, stated at the two spellings of the direct
  image that `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` identifies.
* `AlgebraicGeometry.Space.restrict_eq_zero_of_sectionSupportedIn_of_imageInOpen`: the converse
  of the previous item, needing no closedness of `T` — a section supported on `T` vanishes on
  every subchart lying over `Tᶜ`.  The two together are the kernel description that
  `StacksFrontier/AlgebraicGeometry/Spaces/SupportedSectionsPushforward.lean` keeps private.
* `hasNoSectionsSupportedIn_of_injective_etaleModulePullbackAdjunction_unit`, in the namespace
  `AlgebraicGeometry.Space` like everything else here: a module whose restriction unit along an
  étale morphism missing `T` is injective on the sections over every chart has no sections
  supported on `T`.  This is the reduction of "no sections supported on `T`" to injectivity of
  that unit, which by Stacks 0836 is scheme-theoretic density; everything else is discharged.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_pushforwardModules_of_preimage` and
  `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_modulePushforward_of_preimage`: **a direct
  image inherits having no supported sections.**  For `T` closed and an arbitrary morphism
  `j : V ⟶ X`, if `G` has no nonzero local section supported on `|j|⁻¹T` then `j_*G` has none
  supported on `T`.  This is Stacks 085B again, now at an arbitrary inverse image, and it is the
  hypothesis `hQ` of `AlgebraicGeometry.Space.exists_supportedQuotientIso` at a direct image —
  the space-level counterpart of the scheme-level
  `AlgebraicGeometry.supportedSections_pushforward_eq_zero`.
* `CategoryTheory.Abelian.mono_cokernel_desc_of_isLimit_kernelFork`: in an abelian category, if
  `i` is a kernel of `q` then the induced map `coker i ⟶ Q` is a monomorphism.
* `CategoryTheory.Functor.map_eq_zero_of_eq_zero`: an additive functor carries a vanishing
  morphism to zero, with the functor opaque.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule`:
  **the result.**  For `T` closed, the quotient of `F` by its sections supported on `T` has no
  nonzero local section supported on `T`.

## Implementation notes

**The shape of the argument.**  Let `V ⊆ X` be the open subspace with point set `Tᶜ`, which
exists because `T` is closed (Stacks 03BZ,
`AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints`), and let `η : F ⟶ j_*(F|_V)` be
the unit of Stacks 03LU along its inclusion.  Then

* `η` kills only sections supported on `T`.  A section killed by `η` dies on every chart of `X`
  that factors through `V`
  (`AlgebraicGeometry.Space.restrict_eq_zero_of_etaleModulePullbackAdjunction_unit_eq_zero`); a
  subchart of `W` whose points lie over `Tᶜ` factors through `V` by Stacks 03IE
  (`AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points`), and the factorisation is
  a chart of `V` because `V.ι` is a monomorphism
  (`AlgebraicGeometry.Space.isEtale_of_comp_mono`); so the section dies on every such subchart,
  and is therefore supported on `T`.
* `j_*(F|_V)` has no sections supported on `T`, because no point of `|V|` lies over `T`: by
  Stacks 085B (`AlgebraicGeometry.Space.pushforward_supportedSectionsSubmodule_range_eq`) the
  supported sections of a direct image are the direct image of the sections supported over the
  preimage of `T`, and over an empty preimage a section with empty support is zero
  (`AlgebraicGeometry.Space.eq_zero_of_supportOfSection_eq_empty`).

With those two facts the inclusion of `Γ_T(F)` is a kernel of `η`
(`AlgebraicGeometry.Space.isLimit_kernelFork_supportedSectionsInclusion`), so the induced map
`F/Γ_T(F) ⟶ j_*(F|_V)` is a monomorphism, hence injective on the sections over every chart, and
having no supported sections descends along it
(`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_of_injective`).

**Restriction rather than pullback.**  The adjunction used is
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` (Stacks 03LV) rather than
`AlgebraicGeometry.Space.modulePullbackAdjunction` (Stacks 03D7): the two have the same right
adjoint `AlgebraicGeometry.Space.modulePushforward`, and for the étale one the left adjoint *is*
restriction along `AlgebraicGeometry.Space.smallEtalePostcomp`, so the sections of `F|_V` over a
chart `U` of `V` are the sections of `F` over the composite chart of `X` — both
`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj` and
`AlgebraicGeometry.Space.etaleModulePullback_map_val_app` are `rfl`.

**Elaboration.**  The adjunction and its unit are large terms, and an identity stated directly
at them exceeds the heartbeat ceiling at `whnf`.  Every statement below that mentions the
morphism `j` therefore takes it, its étaleness and the factorisation data as hypotheses and
never unfolds the open subspace; the open subspace is substituted only in the final theorem.
For the same reason the chart factorisation is a separate existence statement rather than
inlined, and the abelian-category step is proved for an arbitrary abelian category.

Two particular rewrites do not elaborate and are replaced by substitution with the large terms
opaque.  Substituting the vanishing of the supported-sections inclusion *underneath*
`pushforwardModules.map` times out at `isDefEq`, so the composite vanishing is obtained once
from `CategoryTheory.Functor.map_eq_zero_of_eq_zero` and transported by `congrArg`.  And
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` is used by substitution
rather than by `rw` on the goal, both for the additivity instance and for the final statement:
after a `rw` at the functor the `Additive` instance is no longer found.

**`Mono` is read on sections through the forgetful functor**, not through
`SheafOfModules.evaluation`: instance search does not find `Mono ((evaluation …).map φ)` at the
small étale ringed site, whereas `SheafOfModules.forget` preserves monomorphisms and
`PresheafOfModules.injective_of_mono` then concludes, which is the pattern of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQuasicoherentRightAdjoint.lean`.

The module universe is `u`, the universe of the schemes: that is where
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` and the cokernels of `𝒪_X`-modules
live.

**No `@[stacks]` attribute is carried, and none should be.**  The vanishing of the supported
sections of the supported-sections quotient is not a numbered result of the Stacks Project at
either level; the source uses it inside the proof of Divisors, Lemma 080E, and the scheme-level
counterpart `AlgebraicGeometry.Scheme.Modules.supportedSections_compl_cokernel_eq_zero` likewise
carries none.  What it is for is Stacks 0864.

## References

* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 085B](https://stacks.math.columbia.edu/tag/085B)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Abelian

/-- **The map out of the cokernel of a kernel is a monomorphism.**  In an abelian category, if
`i : N ⟶ F` is a kernel of `q : F ⟶ Q`, then the morphism `coker i ⟶ Q` induced by `q` is a
monomorphism.

A morphism `a` into `coker i` killed by it is pulled back along the epimorphism `coker.π i`;
the pullback projection to the source of `a` is again an epimorphism, and the other projection
is killed by `q`, hence factors through the kernel `i`, hence dies against `coker.π i`.  So
`a` dies after an epimorphism, and is zero. -/
@[sga "3 IV 5.2.6" "abelian case"]
theorem mono_cokernel_desc_of_isLimit_kernelFork {C : Type*} [Category C] [Abelian C]
    {N F Q : C} (i : N ⟶ F) (q : F ⟶ Q) (w : i ≫ q = 0)
    (hlim : IsLimit (KernelFork.ofι i w)) :
    Mono (cokernel.desc i q w) := by
  refine Preadditive.mono_of_cancel_zero _ fun {A} a ha => ?_
  have hq0 : pullback.snd a (cokernel.π i) ≫ q = 0 := by
    rw [← cokernel.π_desc i q w, ← Category.assoc, ← pullback.condition, Category.assoc, ha,
      comp_zero]
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hlim (pullback.snd a (cokernel.π i)) hq0
  have hfst : pullback.fst a (cokernel.π i) ≫ a = 0 := by
    rw [pullback.condition, ← hl]
    show (l ≫ i) ≫ cokernel.π i = 0
    rw [Category.assoc, cokernel.condition, comp_zero]
  exact zero_of_epi_comp (pullback.fst a (cokernel.π i)) hfst

end CategoryTheory.Abelian

namespace CategoryTheory.Functor

/-- An additive functor carries a morphism which is zero to the zero morphism.  Stated as a
lemma rather than used through `CategoryTheory.Functor.map_zero` so that the substitution of the
vanishing morphism happens with the functor opaque: rewriting underneath `Φ.map` at a concrete
large functor does not elaborate. -/
theorem map_eq_zero_of_eq_zero {C : Type*} {D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] {A A' : C} (f : A ⟶ A') (hf : f = 0) :
    Φ.map f = 0 := by
  rw [hf, Φ.map_zero]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Sections supported on a closed subset, from vanishing over the complement -/

/-- **A section vanishing on the part of its chart over `Tᶜ` is supported on `T`**, for `T`
closed.  Let `X` be an algebraic space over `S`, let `T` be a closed subset of its points, let
`F` be an `𝒪_X`-module and let `s` be a section of `F` over an étale chart `W` of `X`.  If `s`
restricts to zero along every morphism of charts into `W` all of whose points lie over the
complement of `T`, then the support of `s` maps into `T`.

The part of `W` lying over `Tᶜ` is an open subset of the points of the chart because `T` is
closed, and the hypothesis says exactly that it is contained in the open zero locus of `s`, by
the maximality of the latter (`AlgebraicGeometry.Space.largestOpenZeroLocus_maximal`, Stacks
04KA). -/
theorem sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1) (s : F.val.obj (op W))
    (hs : ∀ (U : SmallEtale B S hS X.1) (i : U ⟶ W),
      ImageInOpen B S hS X.1 (pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ) i → F.val.map i.op s = 0) :
    SectionSupportedIn B S hS X.1 X.2 T F W s := by
  let O : TopologicalSpace.Opens
      (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))) :=
    ⟨pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ,
      hT.isOpen_compl.preimage ((pointTopologyFamily B S hS).continuous
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _) X.2 W.1.hom)⟩
  intro x hx
  by_contra hxt
  exact hx
    (largestOpenZeroLocus_maximal B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) W s O hs hxt)

/-- **A section supported on `T` vanishes on the part of its chart over `Tᶜ`** — the converse of
`AlgebraicGeometry.Space.sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen`, and, unlike it,
needing no closedness of `T`.  Let `s` be a section of an `𝒪_X`-module `F` over an étale chart
`W` of `X` whose support maps into `T`.  Then `s` restricts to zero along every morphism of
charts into `W` all of whose points lie over the complement of `T`.

A point of such a chart not landing in the open zero locus of `s` would be a point of its
support — `AlgebraicGeometry.Space.supportOfSection` of Stacks 04KA is by definition the
complement of that open — hence would lie over `T`, which it does not; so the chart lands in the
open zero locus, which is vanishing after restriction by
`AlgebraicGeometry.Space.largestOpenZeroLocus_restrict_iff`.

This is the half of the kernel description that
`StacksFrontier/AlgebraicGeometry/Spaces/SupportedSectionsPushforward.lean` proves and keeps
private, inside its `sectionSupportedIn_iff_restrict_eq_zero`. -/
theorem restrict_eq_zero_of_sectionSupportedIn_of_imageInOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1))
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1) (s : F.val.obj (op W))
    (hs : SectionSupportedIn B S hS X.1 X.2 T F W s)
    (U : SmallEtale B S hS X.1) (i : U ⟶ W)
    (hi : ImageInOpen B S hS X.1 (pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ) i) :
    F.val.map i.op s = 0 :=
  (largestOpenZeroLocus_restrict_iff B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) W s U i).2
    fun x => by
      by_contra hx
      exact hi x (hs hx)

/-! ### Charts factoring through an étale subspace -/

section Factorisation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS}

/-- **A chart of `X` whose structure morphism factors through an étale `j : V ⟶ X` comes from a
chart of `V`.**  Let `j : V ⟶ X` be an étale morphism of algebraic spaces with `j.hom` a
monomorphism, let `i : U ⟶ W` be a morphism of étale charts of `X` and suppose the structure
morphism of `U` factors as `g ≫ j.hom`.  Then `g` is an étale chart `U'` of `V`, and `i`
factors through the composite chart `Φ U'` of `X`, where `Φ` is
`AlgebraicGeometry.Space.smallEtalePostcomp`, by a morphism which is the identity on the
underlying object of the site.

Étaleness of `g` is `AlgebraicGeometry.Space.isEtale_of_comp_mono` followed by
`AlgebraicGeometry.Space.presheafEtale_of_isEtale_yoneda`; the two morphisms of charts are the
identity and `i` on underlying objects, and their triangles over `X` commute by the given
factorisation. -/
theorem exists_factorisation_smallEtalePostcomp (j : V ⟶ X) (hj : IsEtale B S hS j.hom)
    [Mono j.hom] {W U : SmallEtale B S hS X.1} (i : U ⟶ W)
    (g : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U) ⟶ V.1)
    (hg : g ≫ j.hom = U.1.hom) :
    ∃ (U' : SmallEtale B S hS V.1)
      (m : (smallEtalePostcomp B S hS j hj).obj U' ⟶ W)
      (e : U ⟶ (smallEtalePostcomp B S hS j hj).obj U'), e ≫ m = i := by
  have hcomp : IsEtale B S hS (g ≫ j.hom) := by
    rw [hg]
    exact isEtale_of_presheaf_etale B S hS U.property
  have hgE : IsEtale B S hS g := isEtale_of_comp_mono B S hS g j.hom hcomp
  let U' : SmallEtale B S hS V.1 :=
    ⟨CostructuredArrow.mk g, presheafEtale_of_isEtale_yoneda B S hS g hgE⟩
  have hhom : ((smallEtalePostcomp B S hS j hj).obj U').1.hom = U.1.hom := hg
  have hwe : yoneda.map (𝟙 ((SmallEtale.toOver B S hS X.1).obj U)) ≫
      ((smallEtalePostcomp B S hS j hj).obj U').1.hom = U.1.hom := by
    rw [CategoryTheory.Functor.map_id]
    exact (Category.id_comp _).trans hhom
  refine ⟨U', ObjectProperty.homMk (CostructuredArrow.homMk i.hom.left
      ((CostructuredArrow.w i.hom).trans hhom.symm)),
    ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _) hwe), ?_⟩
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.ext
  exact Category.id_comp _

end Factorisation

/-! ### The kernel of the unit of étale restriction -/

/-- **The unit of Stacks 03LU along a subspace carrying every point outside `T` kills only
sections supported on `T`**, for `T` closed.  Let `j : V ⟶ X` be an étale morphism of algebraic
spaces with `j.hom` a monomorphism, through which every morphism from a representable presheaf
into `X` with all points outside `T` factors, and let `F` be an `𝒪_X`-module.  Then a local
section of `F` killed by the unit `F ⟶ j_*(F|_V)` is supported on `T`.

A subchart of `W` all of whose points lie over `Tᶜ` factors through `V` by the hypothesis, hence
comes from a chart of `V` by
`AlgebraicGeometry.Space.exists_factorisation_smallEtalePostcomp`, so the section dies on it by
`AlgebraicGeometry.Space.restrict_eq_zero_of_etaleModulePullbackAdjunction_unit_eq_zero`; and a
section dying on every such subchart is supported on `T` by
`AlgebraicGeometry.Space.sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen`. -/
theorem kernelSectionsSupportedIn_etaleModulePullbackAdjunction_unit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X) (hj : IsEtale B S hS j.hom) [Mono j.hom]
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hfac : ∀ (A : BigFppfOver B S hS) (f : yoneda.obj A ⟶ X.1),
      Set.range (pointsMap B S hS (yoneda.obj A) f) ⊆ Tᶜ → ∃ g, g ≫ j.hom = f)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    KernelSectionsSupportedIn B S hS X T
      ((etaleModulePullbackAdjunction B S hS j hj).unit.app F) := by
  intro W s hs
  refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS X T hT F W s
    fun U i hi => ?_
  have hrange : Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom) ⊆ Tᶜ := by
    rintro y ⟨z, rfl⟩
    have hw : yoneda.map i.hom.left ≫ W.1.hom = U.1.hom := CostructuredArrow.w i.hom
    rw [← hw, pointsMap_comp]
    exact hi z
  obtain ⟨g, hg⟩ := hfac ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom hrange
  obtain ⟨U', m, e, he⟩ := exists_factorisation_smallEtalePostcomp B S hS j hj i g hg
  have h0 : F.val.map m.op s = 0 :=
    restrict_eq_zero_of_etaleModulePullbackAdjunction_unit_eq_zero j hj F W s hs U' m
  have hop : i.op = m.op ≫ e.op := by rw [← he]; rfl
  exact (F.val.congr_map_apply hop s).trans
    ((F.val.map_comp_apply m.op e.op s).trans
      ((congrArg (fun y => F.val.map e.op y) h0).trans (map_zero _)))

/-! ### Direct images along a morphism missing the subset -/

/-- A module with no sections supported on `A` has zero supported-sections inclusion. -/
private theorem supportedSectionsSubmodule_ι_eq_zero_aux
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS) (A : Set (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : HasNoSectionsSupportedIn B S hS Y A G) :
    (supportedSectionsSubmodule B S hS Y.1 Y.2 A G).ι = 0 := by
  ext U x
  exact hG U.unop x.1 ((mem_supportedSectionsSubmodule_iff B S hS Y.1 Y.2 A G U.unop x.1).mp x.2)

/-- **The sections supported on an empty set are zero**, so the inclusion of the submodule of
Stacks 0859 at the empty set is the zero morphism: a section whose support is contained in the
empty preimage of a set has empty support, hence is zero by
`AlgebraicGeometry.Space.eq_zero_of_supportOfSection_eq_empty`. -/
theorem supportedSectionsSubmodule_ι_eq_zero
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS) (A : Set (points B S hS Y.1)) (hA : A = ∅)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (supportedSectionsSubmodule B S hS Y.1 Y.2 A G).ι = 0 :=
  supportedSectionsSubmodule_ι_eq_zero_aux B S hS Y A G fun U x hx =>
    eq_zero_of_supportOfSection_eq_empty (F := moduleAddSheaf B S hS Y.1 Y.2 G) U x
      (Set.subset_empty_iff.1 (hx.trans (by simp [hA])))

/-- A module whose supported-section submodule has only the zero section over every chart has
no sections supported on `T`: a supported section is a section of that submodule, by Stacks
0859. -/
theorem hasNoSectionsSupportedIn_of_range_subset_zero
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} (T : Set (points B S hS X.1))
    (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ W : SmallEtale B S hS X.1,
      Set.range (((supportedSectionsSubmodule B S hS X.1 X.2 T M).ι).val.app (op W)) ⊆ {0}) :
    HasNoSectionsSupportedIn B S hS X T M := fun W s hs =>
  h W ⟨⟨s, (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 T M W s).mpr hs⟩, rfl⟩

/-- The image of the zero morphism of `𝒪`-modules on the sections over a chart is zero. -/
theorem range_val_app_zero_subset
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : AlgebraicSpaces B S hS} (M N : Modules.{u, u} B S hS Y.1 Y.2)
    (W : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Set.range ((0 : M ⟶ N).val.app W) ⊆ {0} := by
  rintro y ⟨t, rfl⟩
  rfl

/-- A direct image along `j` has no sections supported on a closed `T` as soon as the inclusion
of the submodule of sections supported over `|j|⁻¹T` is the zero morphism. -/
theorem hasNoSectionsSupportedIn_pushforwardModules_of_ι_eq_zero
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (G : Modules.{u, u} B S hS V.1 V.2)
    (hι :
      (supportedSectionsSubmodule B S hS V.1 V.2 (pointsMap B S hS V.1 j.hom ⁻¹' T) G).ι = 0) :
    HasNoSectionsSupportedIn B S hS X T
      (((smallEtaleRingedToposHom B S hS j).pushforwardModules).obj G) := by
  have hadd : ((smallEtaleRingedToposHom B S hS j).pushforwardModules).Additive :=
    pushforwardModules_eq_modulePushforward B S hS j ▸
      (inferInstance : (modulePushforward B S hS j).Additive)
  have hmap := Functor.map_eq_zero_of_eq_zero
    ((smallEtaleRingedToposHom B S hS j).pushforwardModules)
    (supportedSectionsSubmodule B S hS V.1 V.2 (pointsMap B S hS V.1 j.hom ⁻¹' T) G).ι
    hι
  refine hasNoSectionsSupportedIn_of_range_subset_zero B S hS T _ fun W => ?_
  rw [← pushforward_supportedSectionsSubmodule_range_eq B S hS j T hT G W]
  exact Set.Subset.trans
    (congrArg (fun φ => Set.range (SheafOfModules.Hom.val φ |>.app (op W))) hmap).subset
    (range_val_app_zero_subset B S hS _ _ _)

/-- **A direct image along a morphism no point of whose source lies over `T` has no sections
supported on `T`**, for `T` closed.  Let `j : V ⟶ X` be a morphism of algebraic spaces over `S`
with `|j|⁻¹T = ∅` and let `G` be an `𝒪_V`-module.  Then every local section of `j_*G` whose
support maps into `T` is zero.

By Stacks 085B (`AlgebraicGeometry.Space.pushforward_supportedSectionsSubmodule_range_eq`) the
sections of `j_*G` supported on `T` are, over every chart, the image of the direct image of the
submodule of sections of `G` supported over `|j|⁻¹T`.  That preimage being empty, such a section
of `G` has empty support, hence is zero
(`AlgebraicGeometry.Space.eq_zero_of_supportOfSection_eq_empty`); so the submodule inclusion
downstairs is the zero morphism, its direct image is zero as the direct image is additive, and
the image in question is `{0}`. -/
theorem hasNoSectionsSupportedIn_pushforwardModules
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hempty : pointsMap B S hS V.1 j.hom ⁻¹' T = ∅)
    (G : Modules.{u, u} B S hS V.1 V.2) :
    HasNoSectionsSupportedIn B S hS X T
      (((smallEtaleRingedToposHom B S hS j).pushforwardModules).obj G) :=
  hasNoSectionsSupportedIn_pushforwardModules_of_ι_eq_zero B S hS j T hT G
    (supportedSectionsSubmodule_ι_eq_zero B S hS V _ hempty G)

/-- **A direct image along a morphism no point of whose source lies over `T` has no sections
supported on `T`**, stated at `AlgebraicGeometry.Space.modulePushforward`, the direct image of
Stacks 03LU.

This is `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_pushforwardModules` transported along
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, which identifies the direct
image attached to the morphism of ringed topoi of Stacks 03G8 with it. -/
theorem hasNoSectionsSupportedIn_modulePushforward
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hempty : pointsMap B S hS V.1 j.hom ⁻¹' T = ∅)
    (G : Modules.{u, u} B S hS V.1 V.2) :
    HasNoSectionsSupportedIn B S hS X T ((modulePushforward B S hS j).obj G) :=
  pushforwardModules_eq_modulePushforward B S hS j ▸
    hasNoSectionsSupportedIn_pushforwardModules B S hS j T hT hempty G

/-! ### Direct images of modules with no supported sections -/

/-- **A module with no sections supported on `A` has only the zero section supported on `A`**, so
the inclusion of the submodule of Stacks 0859 is the zero morphism.  This is
`AlgebraicGeometry.Space.HasNoSectionsSupportedIn` unwound through Stacks 0859;
`AlgebraicGeometry.Space.supportedSectionsSubmodule_ι_eq_zero` is its case of an empty `A`. -/
theorem supportedSectionsSubmodule_ι_eq_zero_of_hasNoSectionsSupportedIn
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS) (A : Set (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : HasNoSectionsSupportedIn B S hS Y A G) :
    (supportedSectionsSubmodule B S hS Y.1 Y.2 A G).ι = 0 :=
  supportedSectionsSubmodule_ι_eq_zero_aux B S hS Y A G hG

/-- **A direct image inherits having no supported sections**, for `T` closed.  Let `j : V ⟶ X`
be a morphism of algebraic spaces over `S` and let `G` be an `𝒪_V`-module with no nonzero local
section supported on the inverse image `|j|⁻¹T`.  Then `j_*G` has no nonzero local section
supported on `T`.

This is the space-level counterpart of the scheme-level
`AlgebraicGeometry.supportedSections_pushforward_eq_zero`, and it is the hypothesis `hQ` of
`AlgebraicGeometry.Space.exists_supportedQuotientIso` at a direct image.  The proof is the one of
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_pushforwardModules`, which is its special case
at an empty inverse image: by Stacks 085B
(`AlgebraicGeometry.Space.pushforward_supportedSectionsSubmodule_range_eq`) the sections of
`j_*G` supported on `T` are, over every chart, the image of the direct image of the submodule of
sections of `G` supported over `|j|⁻¹T`, and that inclusion is the zero morphism by
`AlgebraicGeometry.Space.supportedSectionsSubmodule_ι_eq_zero_of_hasNoSectionsSupportedIn`. -/
theorem hasNoSectionsSupportedIn_pushforwardModules_of_preimage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (G : Modules.{u, u} B S hS V.1 V.2)
    (hG : HasNoSectionsSupportedIn B S hS V (pointsMap B S hS V.1 j.hom ⁻¹' T) G) :
    HasNoSectionsSupportedIn B S hS X T
      (((smallEtaleRingedToposHom B S hS j).pushforwardModules).obj G) :=
  hasNoSectionsSupportedIn_pushforwardModules_of_ι_eq_zero B S hS j T hT G
    (supportedSectionsSubmodule_ι_eq_zero_of_hasNoSectionsSupportedIn B S hS V _ G hG)

/-- **A direct image inherits having no supported sections**, stated at
`AlgebraicGeometry.Space.modulePushforward`, the direct image of Stacks 03LU.

This is `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_pushforwardModules_of_preimage`
transported along `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`. -/
theorem hasNoSectionsSupportedIn_modulePushforward_of_preimage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (G : Modules.{u, u} B S hS V.1 V.2)
    (hG : HasNoSectionsSupportedIn B S hS V (pointsMap B S hS V.1 j.hom ⁻¹' T) G) :
    HasNoSectionsSupportedIn B S hS X T ((modulePushforward B S hS j).obj G) :=
  pushforwardModules_eq_modulePushforward B S hS j ▸
    hasNoSectionsSupportedIn_pushforwardModules_of_preimage B S hS j T hT G hG

/-- **A module whose restriction unit along a morphism missing `T` is injective on sections has
no sections supported on `T`.**  Let `T` be a closed subset of the points of `X`, let
`j : V ⟶ X` be étale with no point of `V` lying over `T`, and let `F` be an `𝒪_X`-module for
which the unit `F ⟶ j_*(F|_V)` of Stacks 03LU is injective on the sections over every étale
chart of `X`.  Then `F` has no nonzero local section supported on `T`.

Both halves of the implication are already in place: a section supported on `T` has image under
the unit again supported on `T` (`AlgebraicGeometry.Space.sectionSupportedIn_map`) and the target
has no such sections (`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_modulePushforward`, the
empty-preimage case), so the image is zero and injectivity returns the section itself.  The whole
content of a statement "`F` has no sections supported on `T`" is therefore the injectivity
hypothesis.

**What `hinj` is not.**  Unconditionally the unit is injective only over the charts of `X` that
come from charts of `V`, by
`AlgebraicGeometry.Space.injective_etaleModulePullbackAdjunction_unit_val_app`; `hinj` asks for
every chart of `X`, and that is a real hypothesis, not a restatement.  For `T`
the point set of an effective Cartier divisor `D` and `V` the open complement of `D` the
corresponding **ring-level** statement is available — scheme-theoretic density of the complement,
`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor`
of Stacks 083S, turned by Stacks 0836
(`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_mono_fSharp`) into monicity of
`fSharp` — but **no result in this library transports that to `hinj`, and this theorem does not
claim it does**.  Doing so needs three things, none of which is proved: a public form of
`mono_fSharp_iff_injective_structureMapApp`, which
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/SchemeTheoreticDensity.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/MonomorphismInjectiveStructureMap.lean` both keep private;
the identification of this unit at `SheafOfModules.unit (structureRingSheaf …)` with
`AlgebraicGeometry.Space.structureSharp`, of which only the sheaf-of-sets analogue
`AlgebraicGeometry.Space.structureSharpSet_eq_unit` exists; and then
`AlgebraicGeometry.Space.moduleChartProjection_app_structureSharp` together with
`AlgebraicGeometry.Space.moduleChartProjection_ext` to compare the two chartwise.  Until then
`hinj` is an input a consumer must supply. -/
theorem hasNoSectionsSupportedIn_of_injective_etaleModulePullbackAdjunction_unit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X) (hjE : IsEtale B S hS j.hom)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hempty : pointsMap B S hS V.1 j.hom ⁻¹' T = ∅)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hinj : ∀ W : SmallEtale B S hS X.1, Function.Injective
      (((etaleModulePullbackAdjunction B S hS j hjE).unit.app F).val.app (op W))) :
    HasNoSectionsSupportedIn B S hS X T F :=
  hasNoSectionsSupportedIn_of_injective T _ hinj
    (hasNoSectionsSupportedIn_modulePushforward B S hS j T hT hempty _)

/-! ### The quotient by the supported sections -/

/-- **The quotient of a module by its sections supported on a closed subset has no sections
supported there.**  Let `X` be an algebraic space over `S`, let `T` be a *closed* subset of its
points and let `F` be an `𝒪_X`-module.  Then every local section of `F/Γ_T(F)` whose support
maps into `T` is zero.

This is the space-level counterpart of
`AlgebraicGeometry.Scheme.Modules.supportedSections_compl_cokernel_eq_zero`, and it is the
hypothesis `hQ` of `AlgebraicGeometry.Space.exists_supportedQuotientIso` and of
`AlgebraicGeometry.Space.exists_strictTransformSheafIso` at the projection onto the quotient.
See the module documentation for the argument. -/
theorem hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    HasNoSectionsSupportedIn B S hS X T
      (cokernel (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι) := by
  set Vsub : Subfunctor X.1 := openSubspaceOfPoints B S hS X.1 Tᶜ with hVsub
  have hVopen : IsOpenSubspace B S hS Vsub :=
    isOpenSubspace_openSubspaceOfPoints B S hS X.2 Tᶜ hT.isOpen_compl
  have hVrange : Set.range (pointsMap B S hS Vsub.toFunctor Vsub.ι) = Tᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ
  set V : AlgebraicSpaces B S hS := ⟨Vsub.toFunctor, hVopen.1⟩ with hV
  set j : V ⟶ X := ObjectProperty.homMk Vsub.ι with hj
  have hjE : IsEtale B S hS j.hom := isEtale_ι_of_isOpenSubspace hVopen
  have _ : Mono j.hom := mono_of_presheaf_isOpenImmersion hVopen.2
  have hempty : pointsMap B S hS V.1 j.hom ⁻¹' T = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    have hyc : pointsMap B S hS Vsub.toFunctor Vsub.ι y ∈ Tᶜ :=
      hVrange ▸ Set.mem_range_self y
    exact hyc hy
  have hfac : ∀ (A : BigFppfOver B S hS) (f : yoneda.obj A ⟶ X.1),
      Set.range (pointsMap B S hS (yoneda.obj A) f) ⊆ Tᶜ → ∃ g, g ≫ j.hom = f := by
    intro A f hf
    exact (factorsThrough_openSubspace_iff_points B S hS X.2
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A) Vsub hVopen f).2
      (by rw [hVrange]; exact hf)
  have hQ : HasNoSectionsSupportedIn B S hS X T
      ((modulePushforward B S hS j).obj ((etaleModulePullback B S hS j hjE).obj F)) :=
    hasNoSectionsSupportedIn_modulePushforward B S hS j T hT hempty _
  have hq : KernelSectionsSupportedIn B S hS X T
      ((etaleModulePullbackAdjunction B S hS j hjE).unit.app F) :=
    kernelSectionsSupportedIn_etaleModulePullbackAdjunction_unit B S hS j hjE T hT hfac F
  have hw := supportedSectionsInclusion_comp_eq_zero T
    ((etaleModulePullbackAdjunction B S hS j hjE).unit.app F) hQ
  set k := cokernel.desc (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι
    ((etaleModulePullbackAdjunction B S hS j hjE).unit.app F) hw with hk
  have hmono : Mono k :=
    Abelian.mono_cokernel_desc_of_isLimit_kernelFork _ _ hw
      (isLimit_kernelFork_supportedSectionsInclusion T _ hq hQ)
  have hfmono : Mono ((SheafOfModules.forget _).map k) := inferInstance
  exact hasNoSectionsSupportedIn_of_injective T k
    (fun W => PresheafOfModules.injective_of_mono ((SheafOfModules.forget _).map k) (op W)) hQ

end AlgebraicGeometry.Space

end

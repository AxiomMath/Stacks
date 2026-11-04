module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequenceSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicArtinRees
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction

/-!
# The global sections of `𝒪_X(-D)|_C`, and the kernel of a thickening restriction

Let `D ⊆ D'` be effective Cartier divisors on a scheme `X` with `D' = D + C`. The short exact
sequence of [Stacks, Tag 0C4T],

`0 ⟶ 𝒪_X(-D)|_C ⟶ 𝒪_{D'} ⟶ 𝒪_D ⟶ 0`,

and the left exactness of global sections identify the kernel of the restriction
`Γ(D', 𝒪) ⟶ Γ(D, 𝒪)` with the global sections of `𝒪_X(-D)|_C`. Taking `D = D ^ (n + 1)`,
`D' = D ^ (n + 2)` and `C = D` this is the cohomological half of the identification of the graded
piece `Iₙ₊₁ / Iₙ₊₂` of the projection-kernel filtration that the Stacks proof of
[Stacks, Tag 0C2K] uses; the other half, internal to the inverse system, is in
`StacksFrontier/AlgebraicGeometry/Surfaces/FormalNeighborhoodGradedPiece.lean`.

## The elaboration cost, and why this file exists

`𝒪_X(-D)|_C` is `i_*i^*ℐ_D` for `i : C ⟶ X` the inclusion of the subscheme, and the sections of
a `Scheme.Modules.pullback` unfold through sheafification colimits. Any defeq check that forces
that unfolding at a *concrete* ideal sheaf — in particular at a power `D ^ (n + 1)`, where the
subscheme is built from the power — exhausts the kernel's budget: applying the existing left
exactness of `Γ` directly to the 0C4T sequence at `D ^ (n + 1) ⊆ D ^ (n + 2) = D ^ (n + 1) + D`
fails with `(kernel) deterministic timeout`. Reducibility attributes do not help, because the
kernel ignores them.

The fix is to name the module, `Stacks.Divisors.restrictedNegativeTwist`, and to prove every
statement about its sections *once*, with the modules and the ideal sheaves free variables, so
that each use is an application the kernel checks by matching rather than by unfolding. The two
presentations of the sections of a closed subscheme's structure sheaf — as sections of the
`𝒪_X`-module `closedSubschemeStructureSheaf` and as sections of the structure sheaf of the
subscheme itself — are definitionally equal but not syntactically so, and each crossing between
them is isolated in a lemma of its own for the same reason.

## The scalars on the kernel

The map of the 0C4T sequence is `𝒪_X`-linear, and `𝒪_X(-D)|_C` is a direct image along the
inclusion `i : C ⟶ X`, so its sections carry an action of `Γ(C, 𝒪_C)` as well. The map is
semilinear for that larger ring too:

`φ (ū · x) = u · φ x` for every `u : Γ(D', 𝒪)` restricting to `ū : Γ(C, 𝒪_C)`.

This does **not** follow from `𝒪_X`-linearity on global sections, because `𝒪_X ⟶ i_*𝒪_C` is
only locally surjective, so a scalar `ū` need not be the restriction of a global function on
`X`. It is proved on an affine cover: over an affine open `U` of `X` the map
`Γ(X, U) ⟶ Γ(C, i⁻¹U)` *is* surjective, and a section `a` of `Γ(X, U)` representing the
restriction of `u` to `V(D') ∩ U` represents the restriction of `ū` as well, by
`Stacks.Divisors.subschemeι_app_eq_restrict_inclusion_appTop`. Over that open the identity is
then the `Γ(X, U)`-linearity of `φ`, and the sheaf condition on `V(D')` finishes. No
multiplicativity of the ideals and no hypothesis on the orders of vanishing enters.

Because the action of `Γ(C, 𝒪_C)` is invisible through the seal on
`Stacks.Divisors.restrictedNegativeTwist`, the semilinear statements are read on the sections of
the pullback itself rather than on the sealed module; the two are the same type.

## Main definitions

* `Stacks.Divisors.restrictedNegativeTwist` — the `𝒪_X`-module `𝒪_X(-D)|_C`, that is the
  restriction of the ideal sheaf of `D` to the subscheme cut out by `C`, pushed forward to `X`.
* `Stacks.Divisors.closedSubschemeSectionsAddEquiv` — the two presentations of the global
  sections of a closed subscheme's structure sheaf, as an additive equivalence.
* `Stacks.Divisors.pushforwardSectionsAddEquiv` — the two presentations of the sections of a
  direct image, as an additive equivalence.
* `Stacks.Divisors.sectionsAddMonoidHom` — the map on global sections of a morphism into the
  structure sheaf of a closed subscheme. This is the map `φ` of the existential results below,
  given a name so that its properties can be stated one at a time.
* `Stacks.Divisors.addEffectiveCartierDivisorSections` — the injection
  `Γ(X, 𝒪_X(-D)|_C) ⟶ Γ(V(C + D), 𝒪)` of [Stacks, Tag 0C4T] on global sections, named.
* `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` — **that injection at
  `D ^ (n + 1) ⊆ D ^ (n + 2)`, named**: the graded piece `Iₙ₊₁ / Iₙ₊₂` inside `Γ(Eₙ₊₂, 𝒪)`. It is
  the previous map followed by restriction along the equality `D * D ^ (n + 1) = D ^ (n + 2)`,
  whose two sides are the same ideal sheaf but not the same term.

## Main results

* `Stacks.Divisors.exists_sections_linearMap_of_shortExact` — left exactness of global sections
  on a short exact sequence of `𝒪_X`-modules, as an injective `Γ(X, U)`-linear map whose image
  is the kernel of the third map.
* `Stacks.Divisors.sectionsAddMonoidHom_injective`, `sectionsAddMonoidHom_eq_iff` and
  `exists_sections_addMonoidHom_of_shortExact` — the same with the middle term the structure
  sheaf of a closed subscheme, read on the subscheme's own global functions.
* `Stacks.Divisors.sectionsAddMonoidHom_smul` — **that map is semilinear for the functions on
  the closed subscheme the direct image lives on.**
* `Stacks.Divisors.exists_sections_linearMap_restrictedNegativeTwist`,
  `exists_sections_addMonoidHom_restrictedNegativeTwist` and
  `exists_sections_addMonoidHom_smul_restrictedNegativeTwist` — those at the short exact
  sequence of [Stacks, Tag 0C4T].
* `Stacks.Divisors.addEffectiveCartierDivisorSections_injective`, `..._eq_iff` and `..._smul`,
  and `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom_injective`, `..._eq_iff` and
  `..._smul` — the three properties of the named maps, one at a time.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_sections_addMonoidHom_ker_thickeningRestriction`
  and `exists_sections_addMonoidHom_smul_ker_thickeningRestriction` — the kernel of
  `Γ(Eₙ₊₂, 𝒪) ⟶ Γ(Eₙ₊₁, 𝒪)` is the image of an injective additive map from
  `Γ(X, 𝒪_X(-D ^ (n + 1))|_D)`, semilinearly over `Γ(E, 𝒪_E)`. The map is
  `gradedSectionsHom`; these are the existential phrasings.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

open AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-! ### Left exactness of global sections, proved once -/

/-- **A composite of module morphisms that vanishes, vanishes on sections.** Stated with all
three modules free variables: the proof ends in a `rfl` that reduces the zero morphism, and that
reduction is affordable only while the modules are opaque. -/
theorem comp_app_eq_zero {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (h : f ≫ g = 0)
    (U : X.Opens) (x : Γ(M, U)) : g.app U (f.app U x) = 0 := by
  have h1 : g.app U (f.app U x) = (f ≫ g).app U x := rfl
  rw [h1, h]
  rfl

/-- **Left exactness of global sections.** For a short exact sequence `0 ⟶ M ⟶ N ⟶ K` of
`𝒪_X`-modules the map `Γ(M, U) ⟶ Γ(N, U)` is an injective `Γ(X, U)`-linear map whose image is
the kernel of `Γ(N, U) ⟶ Γ(K, U)`: evaluation at an open preserves finite limits.

Everything here is a statement about free module variables, so that the uses of this lemma at
the modules of [Stacks, Tag 0C4T] are applications rather than unfoldings. -/
theorem exists_sections_linearMap_of_shortExact {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K)
    (zero : f ≫ g = 0) (hse : (ShortComplex.mk f g zero).ShortExact) (U : X.Opens) :
    ∃ φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U),
      Function.Injective φ ∧ ∀ v, g.app U v = 0 ↔ ∃ x, φ x = v := by
  refine ⟨Scheme.Modules.sectionsLinearMap f U, fun a b hab => ?_, fun v => ⟨?_, ?_⟩⟩
  · exact Stacks.Algebraization.app_injective_of_mono f hse.mono_f U hab
  · intro hv
    exact Stacks.Algebraization.exists_app_eq_of_shortExact _ hse U v hv
  · rintro ⟨x, rfl⟩
    rw [show (Scheme.Modules.sectionsLinearMap f U) x = f.app U x from rfl]
    exact comp_app_eq_zero f g zero U x

/-! ### The two presentations of the functions on a closed subscheme -/

/-- **The global sections of the structure sheaf of a closed subscheme, read two ways.** The
`𝒪_X`-module `closedSubschemeStructureSheaf J` is the direct image of the structure sheaf of
`J.subscheme`, so its sections over `⊤` *are* the global functions on `J.subscheme`. The
identification is the identity; it is given a name because it is not syntactic, and because
every crossing of it has to happen while `J` is a free variable. -/
def closedSubschemeSectionsAddEquiv (J : X.IdealSheafData) :
    Γ(J.closedSubschemeStructureSheaf, (⊤ : X.Opens)) ≃+
      Γ(J.subscheme, (⊤ : J.subscheme.Opens)) :=
  AddEquiv.refl _

/-- The crossing of `Stacks.Divisors.closedSubschemeSectionsAddEquiv` on the zero function. -/
theorem closedSubschemeSections_zero_eq (J : X.IdealSheafData) :
    (0 : Γ(J.closedSubschemeStructureSheaf, (⊤ : X.Opens)))
      = (0 : Γ(J.subscheme, (⊤ : J.subscheme.Opens))) :=
  rfl

/-- **The global sections of a closed subscheme's structure sheaf, as the sections over an
arbitrary open of the ambient scheme.** The same identification as
`Stacks.Divisors.closedSubschemeSectionsAddEquiv`, read over an open `U` of `X` rather than over
`⊤`; at `⊤` the two agree. The general open is what the affine-local arguments below need. -/
def closedSubschemeSectionsAddEquivAt (J : X.IdealSheafData) (U : X.Opens) :
    Γ(J.closedSubschemeStructureSheaf, U) ≃+ Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U) :=
  AddEquiv.refl _

/-- **The sections of a direct image, read as the sections of the source over the preimage.**
The identification is the identity; it is given a name because it is not syntactic, and because
the module structure of the source — over the functions on the source scheme, not on `X` — is
invisible on the direct image. -/
def pushforwardSectionsAddEquiv {Y : Scheme.{u}} (g : Y ⟶ X) (M : Y.Modules) (U : X.Opens) :
    Γ((Scheme.Modules.pushforward g).obj M, U) ≃+ Γ(M, g ⁻¹ᵁ U) :=
  AddEquiv.refl _

/-- `Stacks.Divisors.pushforwardSectionsAddEquiv` over the whole of `X`, with the preimage of
the total open written as the total open. -/
def pushforwardSectionsAddEquivTop {Y : Scheme.{u}} (g : Y ⟶ X) (M : Y.Modules) :
    Γ((Scheme.Modules.pushforward g).obj M, (⊤ : X.Opens)) ≃+ Γ(M, (⊤ : Y.Opens)) :=
  AddEquiv.refl _

/-- The crossing of `Stacks.Divisors.closedSubschemeSectionsAddEquivAt` on a scalar multiple:
the action of `Γ(X, U)` on the structure sheaf of a closed subscheme is multiplication by the
image of the scalar. -/
theorem closedSubschemeSectionsAddEquivAt_smul (J : X.IdealSheafData) (U : X.Opens)
    (a : Γ(X, U)) (v : Γ(J.closedSubschemeStructureSheaf, U)) :
    closedSubschemeSectionsAddEquivAt J U (a • v) =
      (J.subschemeι.app U).hom a * closedSubschemeSectionsAddEquivAt J U v :=
  rfl

/-- **Naturality, on sections, of a morphism from a direct image to the structure sheaf of a
closed subscheme**, read in the two presentations of both sides. Proved with the morphism, the
module and the ideal sheaf free variables. -/
theorem closedSubschemeSectionsAddEquivAt_app_map {Y : Scheme.{u}} (g : Y ⟶ X) {P : Y.Modules}
    {J : X.IdealSheafData}
    (f : (Scheme.Modules.pushforward g).obj P ⟶ J.closedSubschemeStructureSheaf)
    {U V : X.Opens} (i : U ⟶ V) (z : Γ((Scheme.Modules.pushforward g).obj P, V)) :
    (J.subscheme.presheaf.map ((TopologicalSpace.Opens.map J.subschemeι.base).map i).op).hom
        (closedSubschemeSectionsAddEquivAt J V (f.app V z))
      = closedSubschemeSectionsAddEquivAt J U (f.app U
          (P.presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op
            (pushforwardSectionsAddEquiv g P V z))) := by
  have hnat := ConcreteCategory.congr_hom (f.mapPresheaf.naturality i.op) z
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op,
    ConcreteCategory.comp_apply] at hnat
  exact hnat.symm

/-- **A morphism from a direct image is linear for the scalars of the source scheme that come
from the ambient scheme.** This is the `𝒪_X`-linearity of `f`, read through the two
presentations of both sides. -/
theorem closedSubschemeSectionsAddEquivAt_app_smul {Y : Scheme.{u}} (g : Y ⟶ X) {P : Y.Modules}
    {J : X.IdealSheafData}
    (f : (Scheme.Modules.pushforward g).obj P ⟶ J.closedSubschemeStructureSheaf)
    (U : X.Opens) (a : Γ(X, U)) (t : Γ(P, g ⁻¹ᵁ U)) :
    closedSubschemeSectionsAddEquivAt J U (f.app U ((g.app U).hom a • t))
      = (J.subschemeι.app U).hom a * closedSubschemeSectionsAddEquivAt J U (f.app U t) :=
  (congrArg (closedSubschemeSectionsAddEquivAt J U)
      (Scheme.Modules.Hom.app_smul f a t)).trans
    (closedSubschemeSectionsAddEquivAt_smul J U a (f.app U t))

/-- **A global function represented over an open set by a section of the ambient sheaf restricts
to a smaller closed subscheme as that section does.** For `K ≤ L` let `w` be a global function on
`V(K)` and let `z : Γ(X, U)` represent its restriction to `V(K) ∩ U`. Then `z` represents the
restriction to `V(L) ∩ U` of the restriction of `w` to `V(L)`.

This is the one step of the affine-local argument that is not formal: the two opens
`inclusion h ⁻¹ᵁ (K.subschemeι ⁻¹ᵁ U)` and `L.subschemeι ⁻¹ᵁ U` are equal only because
`inclusion h ≫ K.subschemeι = L.subschemeι`, so the equality is proved by rewriting along that
identity before the sections are compared. -/
theorem subschemeι_app_eq_restrict_inclusion_appTop {K L : X.IdealSheafData} (h : K ≤ L)
    (U : X.Opens) (w : Γ(K.subscheme, ⊤)) (z : Γ(X, U))
    (hz : (K.subschemeι.app U).hom z
      = (K.subscheme.presheaf.map (homOfLE le_top).op).hom w) :
    (L.subschemeι.app U).hom z
      = (L.subscheme.presheaf.map (homOfLE le_top).op).hom ((inclusion h).appTop.hom w) := by
  have hnat := congrArg
    (fun φ : Γ(K.subscheme, (⊤ : K.subscheme.Opens)) ⟶ Γ(L.subscheme, _) =>
      (CommRingCat.Hom.hom φ) w)
    (Scheme.Hom.naturality (inclusion h) (U' := (⊤ : K.subscheme.Opens))
      (U := K.subschemeι ⁻¹ᵁ U) (homOfLE le_top).op)
  simp only [CommRingCat.comp_apply] at hnat
  have hcomp : ((inclusion h ≫ K.subschemeι).app U).hom z
      = ((inclusion h).app (K.subschemeι ⁻¹ᵁ U)).hom ((K.subschemeι.app U).hom z) := rfl
  rw [← inclusion_subschemeι h, hcomp, hz]
  exact hnat

/-- **A morphism from a direct image along the immersion of `V(C)` is semilinear for the global
functions on `V(C)`.** If `y` is `ū · x` for a global function `ū` on `V(C)` which is the
restriction of a global function `u` on the smaller closed subscheme `V(K)`, then `f.app ⊤ y` is
`u · f.app ⊤ x`.

Checked over the affine opens `U` of `X`, where `Γ(X, U) ⟶ Γ(V(C), i⁻¹U)` is surjective: a
section `a` representing the restriction of `u` to `V(K) ∩ U` represents the restriction of `ū`
as well, by `Stacks.Divisors.subschemeι_app_eq_restrict_inclusion_appTop`, so over `U` the
identity is the `Γ(X, U)`-linearity of `f`. The affine opens of `X` pull back to a cover of
`V(K)`, so the sheaf condition finishes. -/
theorem app_mul_of_smul_inclusion_appTop {C K : X.IdealSheafData} (hKC : K ≤ C)
    {P : C.subscheme.Modules}
    (f : (Scheme.Modules.pushforward C.subschemeι).obj P ⟶ K.closedSubschemeStructureSheaf)
    (x y : Γ((Scheme.Modules.pushforward C.subschemeι).obj P, (⊤ : X.Opens)))
    (u : Γ(K.subscheme, (⊤ : K.subscheme.Opens)))
    (hy : pushforwardSectionsAddEquivTop C.subschemeι P y =
      (inclusion hKC).appTop.hom u • pushforwardSectionsAddEquivTop C.subschemeι P x) :
    closedSubschemeSectionsAddEquiv K (f.app ⊤ y)
      = u * closedSubschemeSectionsAddEquiv K (f.app ⊤ x) := by
  refine K.subscheme.sheaf.eq_of_locally_eq'
    (fun U : X.affineOpens => K.subschemeι ⁻¹ᵁ U.1) ⊤ (fun _ => homOfLE le_top)
    (le_of_eq (K.subschemeι.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)).symm) _ _ ?_
  intro U
  obtain ⟨a, ha⟩ := K.subschemeι_app_surjective U
    ((K.subscheme.presheaf.map (homOfLE le_top).op).hom u)
  have ha' : (K.subschemeι.app U.1).hom a
      = (K.subscheme.presheaf.map
          (homOfLE (le_top (a := K.subschemeι ⁻¹ᵁ U.1))).op).hom u := ha
  have hb : (C.subscheme.presheaf.map
        (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U.1))).op).hom ((inclusion hKC).appTop.hom u)
      = (C.subschemeι.app U.1).hom a :=
    (subschemeι_app_eq_restrict_inclusion_appTop hKC U.1 u a ha).symm
  have hres : ∀ z : Γ((Scheme.Modules.pushforward C.subschemeι).obj P, (⊤ : X.Opens)),
      (K.subscheme.presheaf.map
            (homOfLE (le_top (a := K.subschemeι ⁻¹ᵁ U.1))).op).hom
          (closedSubschemeSectionsAddEquiv K (f.app ⊤ z))
        = closedSubschemeSectionsAddEquivAt K U.1 (f.app U.1
            (P.presheaf.map (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U.1))).op
              (pushforwardSectionsAddEquivTop C.subschemeι P z))) :=
    fun z => closedSubschemeSectionsAddEquivAt_app_map C.subschemeι f
      (homOfLE (le_top (a := U.1))) z
  have hsmul : P.presheaf.map (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U.1))).op
        (pushforwardSectionsAddEquivTop C.subschemeι P y)
      = (C.subschemeι.app U.1).hom a •
          P.presheaf.map (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U.1))).op
            (pushforwardSectionsAddEquivTop C.subschemeι P x) := by
    rw [hy]
    exact (Scheme.Modules.map_smul P _ _ _).trans (congrArg (· • _) hb)
  refine (hres y).trans ?_
  rw [hsmul, closedSubschemeSectionsAddEquivAt_app_smul C.subschemeι f U.1 a, ha']
  exact (congrArg (_ * ·) (hres x).symm).trans (map_mul _ _ _).symm

/-! ### The map on global sections, named -/

/-- **The map on global sections of a morphism into the structure sheaf of a closed
subscheme.** This is the map `φ` of
`Stacks.Divisors.exists_sections_addMonoidHom_of_shortExact`, given a name so that its
properties — injectivity, its image, and its semilinearity — can be stated one at a time; the
existential results below are corollaries. -/
def sectionsAddMonoidHom {M : X.Modules} {J : X.IdealSheafData}
    (f : M ⟶ J.closedSubschemeStructureSheaf) :
    Γ(M, (⊤ : X.Opens)) →+ Γ(J.subscheme, (⊤ : J.subscheme.Opens)) :=
  (closedSubschemeSectionsAddEquiv J).toAddMonoidHom.comp (f.app ⊤).hom

/-- The crossing of `Stacks.Divisors.closedSubschemeSectionsAddEquiv` on a section in the image
of a morphism into `closedSubschemeStructureSheaf J`. -/
theorem sectionsAddMonoidHom_apply {M : X.Modules} {J : X.IdealSheafData}
    (f : M ⟶ J.closedSubschemeStructureSheaf) (x : Γ(M, (⊤ : X.Opens))) :
    sectionsAddMonoidHom f x = f.app ⊤ x :=
  rfl

/-- **The map on global sections of the first term of a short exact sequence is injective**:
evaluation at an open preserves monomorphisms. -/
theorem sectionsAddMonoidHom_injective {M : X.Modules} {I J : X.IdealSheafData}
    {hsub : J ≤ I} {f : M ⟶ J.closedSubschemeStructureSheaf}
    {zero : f ≫ closedSubschemeRestriction hsub = 0}
    (hse : (ShortComplex.mk f (closedSubschemeRestriction hsub) zero).ShortExact) :
    Function.Injective (sectionsAddMonoidHom f) := fun _ _ hab =>
  Stacks.Algebraization.app_injective_of_mono f hse.mono_f ⊤
    ((closedSubschemeSectionsAddEquiv J).injective hab)

/-- **The image of the map on global sections is the kernel of the restriction.** For a short
exact sequence `0 ⟶ M ⟶ 𝒪_{J} ⟶ 𝒪_{I}` of `𝒪_X`-modules whose third map is the restriction
along `I ⊆ J` of nested closed subschemes, a global function on `J.subscheme` dies on
`I.subscheme` exactly when it comes from `Γ(M, ⊤)`. -/
theorem sectionsAddMonoidHom_eq_iff {M : X.Modules} {I J : X.IdealSheafData}
    (hsub : J ≤ I) (f : M ⟶ J.closedSubschemeStructureSheaf)
    (zero : f ≫ closedSubschemeRestriction hsub = 0)
    (hse : (ShortComplex.mk f (closedSubschemeRestriction hsub) zero).ShortExact)
    (v : Γ(J.subscheme, (⊤ : J.subscheme.Opens))) :
    (inclusion hsub).appTop.hom v = 0 ↔ ∃ x, sectionsAddMonoidHom f x = v := by
  refine ⟨?_, ?_⟩
  · intro hv
    obtain ⟨x, hx⟩ := Stacks.Algebraization.exists_app_eq_of_shortExact _ hse ⊤
      ((closedSubschemeSectionsAddEquiv J).symm v)
      ((closedSubschemeRestriction_appTop hsub
        ((closedSubschemeSectionsAddEquiv J).symm v)).trans hv)
    exact ⟨x, ((sectionsAddMonoidHom_apply f x).trans hx).trans
      ((closedSubschemeSectionsAddEquiv J).apply_symm_apply v)⟩
  · rintro ⟨x, rfl⟩
    exact ((closedSubschemeRestriction_appTop hsub (f.app ⊤ x)).symm.trans
      (comp_app_eq_zero f _ zero ⊤ x)).trans (closedSubschemeSections_zero_eq I)

/-- **The map on global sections is semilinear for the functions on the closed subscheme the
direct image lives on.** This is
`Stacks.Divisors.app_mul_of_smul_inclusion_appTop` for the named map. -/
theorem sectionsAddMonoidHom_smul {C J : X.IdealSheafData} (hJC : J ≤ C)
    {P : C.subscheme.Modules}
    (f : (Scheme.Modules.pushforward C.subschemeι).obj P ⟶ J.closedSubschemeStructureSheaf)
    (u : Γ(J.subscheme, (⊤ : J.subscheme.Opens))) (x : Γ(P, (⊤ : C.subscheme.Opens))) :
    sectionsAddMonoidHom f ((inclusion hJC).appTop.hom u • x) = u * sectionsAddMonoidHom f x :=
  app_mul_of_smul_inclusion_appTop hJC f x ((inclusion hJC).appTop.hom u • x) u rfl

/-- **Left exactness of global sections, read on the subscheme's own functions.** For a short
exact sequence `0 ⟶ M ⟶ 𝒪_{J} ⟶ 𝒪_{I}` of `𝒪_X`-modules whose third map is the restriction
along `I ⊆ J` of nested closed subschemes, the kernel of the ring map
`Γ(J.subscheme, 𝒪) ⟶ Γ(I.subscheme, 𝒪)` is the image of an injective additive map from
`Γ(M, ⊤)`. -/
theorem exists_sections_addMonoidHom_of_shortExact {M : X.Modules} {I J : X.IdealSheafData}
    (hsub : J ≤ I) (f : M ⟶ J.closedSubschemeStructureSheaf)
    (zero : f ≫ closedSubschemeRestriction hsub = 0)
    (hse : (ShortComplex.mk f (closedSubschemeRestriction hsub) zero).ShortExact) :
    ∃ φ : Γ(M, (⊤ : X.Opens)) →+ Γ(J.subscheme, (⊤ : J.subscheme.Opens)),
      Function.Injective φ ∧ ∀ v, (inclusion hsub).appTop.hom v = 0 ↔ ∃ x, φ x = v :=
  ⟨sectionsAddMonoidHom f, sectionsAddMonoidHom_injective hse,
    sectionsAddMonoidHom_eq_iff hsub f zero hse⟩

/-! ### The restriction of a negative twist to an effective Cartier divisor -/

/-- **The module `𝒪_X(-D)|_C`.** The ideal sheaf of `D`, restricted to the subscheme cut out by
`C` and pushed forward to `X`. This is the first term of the short exact sequence of
[Stacks, Tag 0C4T]; it is sealed behind this name so that the elaborator never unfolds a
statement about it through `AlgebraicGeometry.Scheme.Modules.pullback`, whose sections reach
sheafification colimits. -/
def restrictedNegativeTwist (D C : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward C.subschemeι).obj
    ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D))

/-- The definition of `Stacks.Divisors.restrictedNegativeTwist`, the one place where the seal is
opened. Deliberately not a `simp` lemma. -/
theorem restrictedNegativeTwist_eq (D C : X.IdealSheafData) :
    restrictedNegativeTwist D C = (Scheme.Modules.pushforward C.subschemeι).obj
      ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)) :=
  rfl


/-- **The global sections of `𝒪_X(-D)|_C` inject onto the kernel of `Γ(D', 𝒪) ⟶ Γ(D, 𝒪)`**, as
a `Γ(X, ⊤)`-linear map. This is [Stacks, Tag 0C4T] together with the left exactness of global
sections, read on the `𝒪_X`-module `closedSubschemeStructureSheaf D'`. -/
theorem exists_sections_linearMap_restrictedNegativeTwist (D D' C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hD' : IsEffectiveCartierDivisor D')
    (hC : IsEffectiveCartierDivisor C) (hsub : D' ≤ D) (hsum : D' = D * C) :
    ∃ φ : Γ(restrictedNegativeTwist D C, (⊤ : X.Opens)) →ₗ[Γ(X, ⊤)]
        Γ(D'.closedSubschemeStructureSheaf, (⊤ : X.Opens)),
      Function.Injective φ ∧
        ∀ v, (closedSubschemeRestriction hsub).app ⊤ v = 0 ↔ ∃ x, φ x = v := by
  rw [restrictedNegativeTwist_eq]
  obtain ⟨f, zero, hse⟩ := addEffectiveCartierDivisor_shortExact D D' C hD hD' hC hsub hsum
  exact exists_sections_linearMap_of_shortExact f _ zero hse ⊤

/-- **The global sections of `𝒪_X(-D)|_C` inject onto the kernel of the restriction of global
functions `Γ(D', 𝒪) ⟶ Γ(D, 𝒪)`.** The same as
`Stacks.Divisors.exists_sections_linearMap_restrictedNegativeTwist`, read on the global functions
of the subschemes themselves rather than on the `𝒪_X`-modules they define. -/
theorem exists_sections_addMonoidHom_restrictedNegativeTwist (D D' C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hD' : IsEffectiveCartierDivisor D')
    (hC : IsEffectiveCartierDivisor C) (hsub : D' ≤ D) (hsum : D' = D * C) :
    ∃ φ : Γ(restrictedNegativeTwist D C, (⊤ : X.Opens)) →+
        Γ(D'.subscheme, (⊤ : D'.subscheme.Opens)),
      Function.Injective φ ∧ ∀ v, (inclusion hsub).appTop.hom v = 0 ↔ ∃ x, φ x = v := by
  rw [restrictedNegativeTwist_eq]
  obtain ⟨f, zero, hse⟩ := addEffectiveCartierDivisor_shortExact D D' C hD hD' hC hsub hsum
  exact exists_sections_addMonoidHom_of_shortExact hsub f zero hse

/-- **The injection of `Stacks.Divisors.exists_sections_addMonoidHom_restrictedNegativeTwist` is
semilinear over the functions on `C`.** Beyond injectivity and the identification of its image
with the kernel of `Γ(D', 𝒪) ⟶ Γ(D, 𝒪)`, the map satisfies `φ (ū · x) = u · φ x` for every
global function `u` on `V(D')` and its restriction `ū` to `V(C)`.

The sections of `𝒪_X(-D)|_C` are written here as the sections over `V(C)` of the pullback of
the ideal sheaf rather than as the sections of the sealed module
`Stacks.Divisors.restrictedNegativeTwist`: the two are the same type, but the action of
`Γ(V(C), 𝒪)` — the one the statement is about — is visible only on the former. -/
theorem exists_sections_addMonoidHom_smul_restrictedNegativeTwist (D D' C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hD' : IsEffectiveCartierDivisor D')
    (hC : IsEffectiveCartierDivisor C) (hsub : D' ≤ D) (hsubC : D' ≤ C) (hsum : D' = D * C) :
    ∃ φ : Γ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D),
          (⊤ : C.subscheme.Opens)) →+ Γ(D'.subscheme, (⊤ : D'.subscheme.Opens)),
      Function.Injective φ ∧
      (∀ v, (inclusion hsub).appTop.hom v = 0 ↔ ∃ x, φ x = v) ∧
      (∀ u x, φ ((inclusion hsubC).appTop.hom u • x) = u * φ x) := by
  obtain ⟨f, zero, hse⟩ := addEffectiveCartierDivisor_shortExact D D' C hD hD' hC hsub hsum
  exact ⟨sectionsAddMonoidHom f, sectionsAddMonoidHom_injective hse,
    sectionsAddMonoidHom_eq_iff hsub f zero hse, sectionsAddMonoidHom_smul hsubC f⟩

/-! ### The injection of [Stacks, Tag 0C4T] on global sections, named -/

/-- **The injection `Γ(X, 𝒪_X(-D)|_C) ⟶ Γ(V(C + D), 𝒪)` of [Stacks, Tag 0C4T], named.** It is
the named map `Stacks.Divisors.sumKernelMap` of that sequence read on global
sections, so it is not a choice: the maps belonging to two different divisors `D` can be
compared, which is what an `Exists.choose` makes impossible.

The sum is written `C * D`, the spelling the named map has, rather than as a separate divisor
`D'` with an equation; a user at a `D'` given by an equation crosses to it by restricting along
that equality, `AlgebraicGeometry.Scheme.IdealSheafData.inclusion_appTop_inclusion_appTop_of_eq`.
-/
def addEffectiveCartierDivisorSections (C D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) :
    Γ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D), (⊤ : C.subscheme.Opens)) →+
      Γ((C * D).subscheme, (⊤ : (C * D).subscheme.Opens)) :=
  sectionsAddMonoidHom (sumKernelMap D C hD)

/-- The named injection of [Stacks, Tag 0C4T] on global sections is injective. -/
theorem addEffectiveCartierDivisorSections_injective (C D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) :
    Function.Injective (addEffectiveCartierDivisorSections C D hD) :=
  sectionsAddMonoidHom_injective (shortExact_sumKernelMap D C hD hsub)

/-- **The image of the named injection is the kernel of `Γ(V(C + D), 𝒪) ⟶ Γ(V(D), 𝒪)`.** -/
theorem addEffectiveCartierDivisorSections_eq_iff (C D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D)
    (v : Γ((C * D).subscheme, (⊤ : (C * D).subscheme.Opens))) :
    (inclusion hsub).appTop.hom v = 0 ↔
      ∃ x, addEffectiveCartierDivisorSections C D hD x = v :=
  sectionsAddMonoidHom_eq_iff hsub (sumKernelMap D C hD)
    (sumKernelMap_comp_closedSubschemeRestriction D C hD hsub)
    (shortExact_sumKernelMap D C hD hsub) v

/-- **The named injection is semilinear over the global functions on `C`.** -/
theorem addEffectiveCartierDivisorSections_smul (C D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsubC : C * D ≤ C)
    (u : Γ((C * D).subscheme, (⊤ : (C * D).subscheme.Opens)))
    (x : Γ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D),
      (⊤ : C.subscheme.Opens))) :
    addEffectiveCartierDivisorSections C D hD ((inclusion hsubC).appTop.hom u • x) =
      u * addEffectiveCartierDivisorSections C D hD x :=
  sectionsAddMonoidHom_smul hsubC (sumKernelMap D C hD) u x

end Stacks.Divisors

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Stacks.Divisors

variable {X : Scheme.{u}}

/-- **The kernel of the restriction `Γ(Eₙ₊₂, 𝒪) ⟶ Γ(Eₙ₊₁, 𝒪)` between the infinitesimal
thickenings of an effective Cartier divisor is the image of `Γ(X, 𝒪_X(-D ^ (n + 1))|_D)`.** This
is [Stacks, Tag 0C4T] for `D ^ (n + 2) = D ^ (n + 1) + D` together with the left exactness of
global sections; it is the cohomological half of the identification of the graded piece
`Iₙ₊₁ / Iₙ₊₂` of the projection-kernel filtration used by the Stacks proof of
[Stacks, Tag 0C2K]. -/
theorem exists_sections_addMonoidHom_ker_thickeningRestriction (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    ∃ φ : Γ(restrictedNegativeTwist (D ^ (n + 1)) D, (⊤ : X.Opens)) →+
        Γ(thickening D (n + 1), (⊤ : (thickening D (n + 1)).Opens)),
      Function.Injective φ ∧ ∀ v, thickeningRestriction D n v = 0 ↔ ∃ x, φ x = v :=
  exists_sections_addMonoidHom_restrictedNegativeTwist (D ^ (n + 1)) (D ^ (n + 2)) D
    inferInstance inferInstance inferInstance (pow_succ_le_pow_succ D (Nat.le_succ n))
    (pow_succ D (n + 1))

/-! ### The injection of the graded piece, named -/

/-- **The injection `Γ(X, 𝒪_X(-D ^ (n + 1))|_D) ⟶ Γ(Eₙ₊₂, 𝒪)` of [Stacks, Tag 0C4T], named.**
It is `Stacks.Divisors.addEffectiveCartierDivisorSections` at `C = D` and the divisor
`D ^ (n + 1)`, whose sum is `D * D ^ (n + 1)`, followed by restriction along the equality
`D * D ^ (n + 1) = D ^ (n + 2)` of
`Stacks.Divisors.mul_pow_succ_eq`: the two ideal sheaves are equal but
are not the same term, and the subschemes they cut out are therefore different terms with the
same global functions.

Being named rather than chosen is what lets the injections in two different degrees appear in
one statement. -/
def gradedSectionsHom (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (n : ℕ) :
    Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
        (⊤ : D.subscheme.Opens)) →+ Γ(thickening D (n + 1), ⊤) :=
  ((inclusion (Stacks.Divisors.mul_pow_succ_eq D n).le).appTop.hom.toAddMonoidHom).comp
    (addEffectiveCartierDivisorSections D (D ^ (n + 1)) inferInstance)

/-- `gradedSectionsHom D n x` is the restriction, along `D * D ^ (n + 1) = D ^ (n + 2)`, of
`addEffectiveCartierDivisorSections D (D ^ (n + 1)) x`. -/
theorem gradedSectionsHom_apply (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (n : ℕ)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) :
    gradedSectionsHom D n x =
      (inclusion (Stacks.Divisors.mul_pow_succ_eq D n).le).appTop.hom
        (addEffectiveCartierDivisorSections D (D ^ (n + 1)) inferInstance x) :=
  rfl

/-- The sum `D * D ^ (n + 1)` is contained in `D ^ (n + 1)`: restriction along it is the
right-hand map of the 0C4T sequence. -/
theorem self_mul_pow_succ_le_pow_succ (D : X.IdealSheafData) (n : ℕ) :
    D * D ^ (n + 1) ≤ D ^ (n + 1) :=
  (Stacks.Divisors.mul_pow_succ_eq D n).le.trans (pow_succ_le_pow_succ D (Nat.le_succ n))

/-- The sum `D * D ^ (n + 1)` is contained in `D`: restriction along it is the scalar of the
semilinearity. -/
theorem self_mul_pow_succ_le_self (D : X.IdealSheafData) (n : ℕ) : D * D ^ (n + 1) ≤ D :=
  (Stacks.Divisors.mul_pow_succ_eq D n).le.trans (pow_succ_le_self D (n + 1))

/-- The map `gradedSectionsHom D n` is injective. -/
theorem gradedSectionsHom_injective (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (n : ℕ) : Function.Injective (gradedSectionsHom D n) := by
  intro a b hab
  have hEq := Stacks.Divisors.mul_pow_succ_eq D n
  refine addEffectiveCartierDivisorSections_injective D (D ^ (n + 1)) inferInstance
    (self_mul_pow_succ_le_pow_succ D n) ?_
  simpa only [gradedSectionsHom_apply, inclusion_appTop_inclusion_appTop_of_eq hEq] using
    congrArg (inclusion hEq.ge).appTop.hom hab

/-- **The image of the named injection is the kernel of `Γ(Eₙ₊₂, 𝒪) ⟶ Γ(Eₙ₊₁, 𝒪)`.** -/
theorem gradedSectionsHom_eq_iff (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (n : ℕ)
    (v : Γ(thickening D (n + 1), ⊤)) :
    thickeningRestriction D n v = 0 ↔ ∃ x, gradedSectionsHom D n x = v := by
  have hEq := Stacks.Divisors.mul_pow_succ_eq D n
  have hsub := self_mul_pow_succ_le_pow_succ D n
  refine ⟨fun hv => ?_, ?_⟩
  · have h0 : (inclusion hsub).appTop.hom ((inclusion hEq.ge).appTop.hom v) = 0 := by
      rw [inclusion_appTop_inclusion_appTop hEq.ge hsub v,
        ← thickeningRestriction_eq_inclusion_appTop D n (hEq.ge.trans hsub) v]
      exact hv
    obtain ⟨x, hx⟩ := (addEffectiveCartierDivisorSections_eq_iff D (D ^ (n + 1)) inferInstance
      hsub _).1 h0
    refine ⟨x, ?_⟩
    rw [gradedSectionsHom_apply, hx]
    exact inclusion_appTop_inclusion_appTop_of_eq_symm hEq v
  · rintro ⟨x, rfl⟩
    rw [gradedSectionsHom_apply,
      thickeningRestriction_eq_inclusion_appTop D n (pow_succ_le_pow_succ D (Nat.le_succ n)),
      inclusion_appTop_inclusion_appTop hEq.le (pow_succ_le_pow_succ D (Nat.le_succ n))]
    exact (addEffectiveCartierDivisorSections_eq_iff D (D ^ (n + 1)) inferInstance hsub _).2
      ⟨x, rfl⟩

/-- **The named injection is semilinear over the global functions on `E`.** -/
theorem gradedSectionsHom_smul (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (n : ℕ)
    (u : Γ(thickening D (n + 1), ⊤))
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) :
    gradedSectionsHom D n ((inclusion (pow_succ_le_self D (n + 1))).appTop.hom u • x) =
      u * gradedSectionsHom D n x := by
  have hEq := Stacks.Divisors.mul_pow_succ_eq D n
  have hsubC := self_mul_pow_succ_le_self D n
  rw [gradedSectionsHom_apply, gradedSectionsHom_apply,
    ← inclusion_appTop_inclusion_appTop hEq.ge hsubC u,
    addEffectiveCartierDivisorSections_smul D (D ^ (n + 1)) inferInstance hsubC, map_mul,
    inclusion_appTop_inclusion_appTop_of_eq_symm hEq u]

/-- **That injection is semilinear over the global functions on `E`.** Beyond injectivity and
the identification of its image with the kernel of `Γ(Eₙ₊₂, 𝒪) ⟶ Γ(Eₙ₊₁, 𝒪)`, the map of
`AlgebraicGeometry.Scheme.IdealSheafData`
`.exists_sections_addMonoidHom_ker_thickeningRestriction` satisfies `φ (ū · x) = u · φ x` for
every global function `u` on `Eₙ₊₁` and its restriction `ū` to `E`.

This is the scalar compatibility that the identification of the graded piece `Iₙ₊₁ / Iₙ₊₂` of
the projection-kernel filtration with a `k`-vector space needs: the `k`-action on the sections
comes from `Γ(E, 𝒪_E)`, while the action on the graded piece is multiplication inside
`Γ(Eₙ₊₁, 𝒪)`. -/
theorem exists_sections_addMonoidHom_smul_ker_thickeningRestriction (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    ∃ φ : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
          (⊤ : D.subscheme.Opens)) →+
        Γ(thickening D (n + 1), (⊤ : (thickening D (n + 1)).Opens)),
      Function.Injective φ ∧
      (∀ v, thickeningRestriction D n v = 0 ↔ ∃ x, φ x = v) ∧
      (∀ u x, φ ((inclusion (pow_succ_le_self D (n + 1))).appTop.hom u • x) = u * φ x) :=
  ⟨gradedSectionsHom D n, gradedSectionsHom_injective D n, gradedSectionsHom_eq_iff D n,
    gradedSectionsHom_smul D n⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end

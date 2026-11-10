module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.AffineCase
public import StacksFrontier.AlgebraicGeometry.Algebraization.CanonicalExtensionMittagLeffler
public import StacksFrontier.AlgebraicGeometry.Algebraization.CechSectionsTorsionAlgebraization
public import StacksFrontier.AlgebraicGeometry.Algebraization.GlobalSectionsComparison
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CanonicalExtensionBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.MittagLefflerCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.GradedQuotients
public import StacksFrontier.CategoryTheory.Limits.ProObject.Ladder
public import StacksFrontier.RingTheory.AdicCompletion.LadderGradedAlgebraization
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.GradedComplement

/-!
# Graded algebraization of a formal module on the punctured spectrum

In the algebraization situation of a graded Noetherian ring `A` with irrelevant ideal `𝔞 = A₊`
and homogeneous `I`, let `(ℱₙ)` be a coherent `I`-adic system on `U = Spec(A) ∖ V(𝔞)` presented by
an inverse system `(Mₙ)` of graded `A`-modules, and suppose it extends canonically to
`X = Spec(A)`. This file produces a finite graded `A`-module `N` whose adic quotients are linked to
`(Mₙ)` by degree-preserving maps, modulo `𝔞`-power torsion, and whose associated coherent module
has `(ℱₙ)` for its completion.

The system `(Hₙ) = (Γ(U, ℱₙ))` is graded because `(ℱₙ)` is presented by a graded system: the
grading comes from the graded Čech model, and its transitions preserve degrees because the
restriction maps do and the sections on `U` carry no `𝔞`-power torsion. The canonical extension
gives a ladder from `(Hₙ)` to the adic tower `(Γ(X, 𝒢ₙ))` of finite modules, from which the
reindexed stable images of `(Hₙ)` are a graded adic tower, and the graded limit theorem of
Stacks 0EKC turns that into a single finite graded module `N`. The restriction maps
`Mₙ → Hₙ` have `𝔞`-power torsion kernel and cokernel (Stacks 0BK0), and `(Hₙ)` is linked to
`(N/Iⁿ⁺¹N)` by a ladder of degree-preserving maps.

The completion statement reads the same ladders on limits. The graded adic tower and the system
`(Γ(X, 𝒢ₙ))` are adic towers linked by a chain of two ladders, hence have the same limit, hence
the same terms: `N/Iⁿ⁺¹N ≅ Γ(X, 𝒢ₙ)`, compatibly with the transitions. Sheafifying that
isomorphism and restricting to `U` identifies the `n`-th term of the completion of `N^~|_U` with
`ℱₙ`, because the sheafification of `Γ(X, 𝒢ₙ)` is `𝒢ₙ` and the canonical extension restricts on
`U` to `(ℱₙ)`.

This replaces the `𝐆ₘ`-equivariant descent of the source's proof by the elementary stabilization
of the stable images, which already sees the grading.

## Main definitions

* `Stacks.Algebraization.tildeCoherentModule` — the coherent `𝒪_X`-module `N^~` of a finite
  `A`-module `N`.

## Main results

* `Stacks.Algebraization.nonempty_restrictionIso_of_proIso` — a coherent adic system on `X`
  pro-isomorphic to the sheaves associated to the global sections of `(ℱₙ)` restricts on `U` to
  `(ℱₙ)`.
* `Stacks.Algebraization.complementRes_eq_complementRestriction`,
  `Stacks.Algebraization.isIPowerTorsion_ker_complementRes`,
  `Stacks.Algebraization.isIPowerTorsion_quotient_range_complementRes` — the restriction map
  `Stacks.LocalCohomology.complementRes` is the 0BK0 comparison.
* `Stacks.Algebraization.exists_linearEquiv_of_limitIso_isAdicTower` — two adic towers with the
  same limit have the same terms, compatibly with the transition maps.
* `Stacks.Algebraization.extensionSectionsTildeIso` — a coherent adic system on the affine `X`
  is the sheafification of its system of global sections.
* `Stacks.Algebraization.nonempty_completionIso_of_adicQuotientsEquiv` — `(ℱₙ)` is the completion
  of `N^~|_U` once the adic quotients of `N` are identified with an inverse system whose
  sheafifications restrict on `U` to `(ℱₙ)`.
* `Stacks.Algebraization.exists_finite_graded_ladder_of_canonicallyExtends` — the finite graded
  module `N`, with its adic quotients linked to `(Mₙ)` by explicit degree-preserving data and with
  `(ℱₙ)` the completion of `N^~|_U`.
* `Stacks.Algebraization.exists_finite_graded_proIso_completion_of_canonicallyExtends` —
  **Stacks 0EL4**: the adic quotients of `N` are pro-isomorphic to `(Mₙ)` in the category of
  graded `A`-modules modulo `A₊`-power torsion modules, and `(ℱₙ)` is the completion of the
  coherent module associated to `N`.

## References

* [Stacks Project, Tag 0EL4](https://stacks.math.columbia.edu/tag/0EL4)
* [Stacks Project, Tag 0EKC](https://stacks.math.columbia.edu/tag/0EKC)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Stacks.LocalCohomology

open scoped Pointwise

attribute [local instance] instVAddNatIntGradedLocalizedModule

universe u v w

namespace Stacks.Algebraization

/-! ### The restriction of a canonical extension -/

/-- **The restriction of a canonical extension, at a given extension.** If the quasi-coherent
sheaves associated to the global sections of `(ℱₙ)` are pro-isomorphic to the coherent adic
system `(𝒢ₙ)` on `X`, and if those sheaves restrict on `U` to `(ℱₙ)` itself, then the termwise
restriction of `(𝒢ₙ)` to `U` is `(ℱₙ)`.

Restriction along `U ⟶ X` carries the pro-isomorphism to a pro-isomorphism on `U`, whose source
is the pro-object of `(ℱₙ)` by the comparison `hsections` and whose target is the pro-object of
the termwise restriction of `(𝒢ₙ)`; two objects of `Coh(U, I𝒪_U)` presenting the same pro-object
are isomorphic, the pro-object functor being fully faithful. -/
public theorem nonempty_restrictionIso_of_proIso (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hsections : tildeGlobalSectionsSystem S F ⋙
        Stacks.Coherent.quasicoherentModulesPullback S.U.ι ≅
      Stacks.Coherent.quasicoherentDiagram F)
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S))
    (e : Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
      (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G) :
    Nonempty (G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι ≅ F.obj) := by
  obtain ⟨e'⟩ := Stacks.Coherent.nonempty_diagramToPro_comp_iso
    (Stacks.Coherent.quasicoherentModulesPullback S.U.ι)
    (tildeGlobalSectionsSystem S F) (Stacks.Coherent.quasicoherentDiagram G) e
  let G' : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S) :=
    (Stacks.Coherent.coherentAdicPullback S.U.ι (idealOnX S)).obj G
  have hdiag : Stacks.Coherent.quasicoherentDiagram G' =
      Stacks.Coherent.quasicoherentDiagram G ⋙
        Stacks.Coherent.quasicoherentModulesPullback S.U.ι :=
    Stacks.Coherent.coherentAdicPullback_quasicoherentDiagram S.U.ι (idealOnX S) G
  have key : (Stacks.Coherent.coherentAdicToPro S.U.toScheme (idealOnOpen S)).obj F ≅
      (Stacks.Coherent.coherentAdicToPro S.U.toScheme (idealOnOpen S)).obj G' :=
    (Stacks.Coherent.diagramToProMapIso hsections).symm ≪≫ e' ≪≫
      eqToIso (congrArg Stacks.Coherent.diagramToPro hdiag).symm
  obtain ⟨hff⟩ :=
    Stacks.Coherent.coherentAdicToPro_fullyFaithful S.U.toScheme (idealOnOpen S)
  exact ⟨Functor.isoWhiskerLeft G.obj (Scheme.Modules.restrictFunctorIsoPullback S.U.ι) ≪≫
    ((ObjectProperty.ι _).mapIso (hff.preimageIso key)).symm⟩

/-- A surjection with kernel `J • ⊤` identifies the quotient by `J • ⊤` with its target,
compatibly with the quotient map. -/
private theorem exists_quotient_smul_top_equiv {A : Type u} [CommRing A] {P Q : Type w}
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] (J : Ideal A) (f : P →ₗ[A] Q)
    (hsurj : Function.Surjective f) (hker : LinearMap.ker f = J • (⊤ : Submodule A P)) :
    ∃ e : (P ⧸ J • (⊤ : Submodule A P)) ≃ₗ[A] Q,
      ∀ x : P, e (Submodule.Quotient.mk x) = f x :=
  ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj),
    fun x => by simp [LinearMap.quotKerEquivOfSurjective_apply_mk]⟩

/-- A module with at most one element is `I`-power torsion. -/
private theorem isIPowerTorsion_of_subsingleton {R : Type u} [CommRing R] {P : Type w}
    [AddCommGroup P] [Module R P] [Subsingleton P] (I : Ideal R) : IsIPowerTorsion R P I :=
  fun m => ⟨1, Nat.one_pos, fun a _ => by rw [Subsingleton.elim m 0, smul_zero]⟩

/-! ### Bridges to the geometric vocabulary on `U` -/

/-- The `A`-module of sections on `U` of the restriction of `P^~` along `U ⟶ Spec(A)` is the
`A`-module `Γ(U, P^~|U)` of the local-cohomology development: the geometric vocabulary of
`Stacks.Algebraization.globalSectionsSystem` and the sheaf-theoretic vocabulary of
`Stacks.LocalCohomology.complementGlobalSections` name the same object. -/
public theorem restrictTilde_sections_eq (S : AlgebraizationSituation.{u}) (P : ModuleCat.{u} S.A) :
    (_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars (scalarMap S)).obj
      ((Scheme.Modules.restrictFunctor S.U.ι).obj ((tilde.functor (.of S.A)).obj P)) =
      Stacks.LocalCohomology.complementGlobalSections S.A S.a
        (Stacks.LocalCohomology.complementTilde S.A S.a P) :=
  rfl

/-- The restriction map `P → Γ(U, P^~|U)` of the local-cohomology development is the comparison
map of the algebraization situation, taken with the identity identification of the sheaf on `U`.
Both send `m` to the constant fraction `m/1`. -/
public theorem complementRes_eq_complementRestriction (S : AlgebraizationSituation.{u})
    (P : ModuleCat.{u} S.A) :
    Stacks.LocalCohomology.complementRes (M := P) S.a =
      S.complementRestriction.{u, u} P
        (Stacks.LocalCohomology.complementTilde S.A S.a P) (Iso.refl _) := by
  refine LinearMap.ext fun m => ?_
  change _ = restrictionToComplement _ P _ (Iso.refl _) m
  rw [restrictionToComplement_apply]
  rfl

/-- **Stacks Project, Tag 0BK0, for the restriction map on sections.** The kernel of
`P → Γ(U, P^~|U)` is `𝔞`-power torsion. -/
public theorem isIPowerTorsion_ker_complementRes (S : AlgebraizationSituation.{u})
    (P : ModuleCat.{u} S.A) :
    IsIPowerTorsion S.A (LinearMap.ker
      (Stacks.LocalCohomology.complementRes (M := P) S.a)) S.a := by
  rw [complementRes_eq_complementRestriction]
  exact isIPowerTorsion_ker_complementRestriction S P _ (Iso.refl _)

/-- **Stacks Project, Tag 0BK0, for the restriction map on sections.** The cokernel of
`P → Γ(U, P^~|U)` is `𝔞`-power torsion. -/
public theorem isIPowerTorsion_quotient_range_complementRes (S : AlgebraizationSituation.{u})
    (P : ModuleCat.{u} S.A) :
    IsIPowerTorsion S.A (Stacks.LocalCohomology.complementGlobalSections S.A S.a
      (Stacks.LocalCohomology.complementTilde S.A S.a P) ⧸
        LinearMap.range (Stacks.LocalCohomology.complementRes (M := P) S.a)) S.a := by
  rw [complementRes_eq_complementRestriction]
  exact isIPowerTorsion_quotient_range_complementRestriction S P _ (Iso.refl _)

/-- The restriction map `P → Γ(U, P^~|U)` is natural in `P`: a module map acts on sections by
applying it to numerators, so it carries the constant fraction `m/1` to `φ m / 1`. -/
public theorem complementRes_naturality (S : AlgebraizationSituation.{u})
    {P Q : ModuleCat.{u} S.A} (φ : P ⟶ Q) (m : P) :
    ((_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars (scalarMap S)).map
      ((Scheme.Modules.restrictFunctor S.U.ι).map ((tilde.functor (.of S.A)).map φ))).hom
        (Stacks.LocalCohomology.complementRes (M := P) S.a m) =
      Stacks.LocalCohomology.complementRes (M := Q) S.a (φ.hom m) :=
  Subtype.ext (funext fun _ => IsLocalizedModule.map_LocalizedModules _ _ _ _)

/-! ### A ladder between two adic towers is a levelwise isomorphism -/

open Stacks.ProObject CategoryTheory.Limits in
/-- **Two adic towers with the same limit agree level by level.** An adic tower is the system of
quotients of its own inverse limit by the powers of `I`
(`Stacks.Coherent.moduleLimit_projection_ker`), so an isomorphism of the limits descends to an
isomorphism of the towers at every level, compatibly with their transition maps. -/
public theorem exists_linearEquiv_of_limitIso_isAdicTower
    {R : Type u} [CommRing R] {D E : ℕᵒᵖ ⥤ ModuleCat.{u} R} {I : Ideal R} (hI : I.FG)
    (hD : IsAdicTower I D) (hE : IsAdicTower I E)
    (e : (limit D : ModuleCat.{u} R) ≅ (limit E : ModuleCat.{u} R)) :
    ∃ φ : ∀ j : ℕ, D.obj (op j) ≃ₗ[R] E.obj (op j),
      ∀ (j l : ℕ) (h : j ≤ l) (x : D.obj (op l)), tr E h (φ l x) = φ j (tr D h x) := by
  have hsD : ∀ j : ℕ, Function.Surjective ((limit.π D (op j)).hom) :=
    fun j => Stacks.Coherent.moduleLimit_projection_surjective D hD.surjective j
  have hkD : ∀ j : ℕ, LinearMap.ker ((limit.π D (op j)).hom) =
      I ^ (j + 1) • (⊤ : Submodule R (limit D : ModuleCat.{u} R)) :=
    fun j => Stacks.Coherent.moduleLimit_projection_ker D hD.surjective hD.ker hI j
  -- the projections of `E`, read through the identification of the limits
  have hsE : ∀ j : ℕ, Function.Surjective ((e.hom ≫ limit.π E (op j)).hom) := by
    intro j y
    obtain ⟨z, hz⟩ := Stacks.Coherent.moduleLimit_projection_surjective E hE.surjective j y
    obtain ⟨w, hw⟩ := e.toLinearEquiv.surjective z
    exact ⟨w, by
      change ((limit.π E (op j)).hom) (e.hom.hom w) = y
      rw [show e.hom.hom w = z from hw]
      exact hz⟩
  have hkE : ∀ j : ℕ, LinearMap.ker ((e.hom ≫ limit.π E (op j)).hom) =
      I ^ (j + 1) • (⊤ : Submodule R (limit D : ModuleCat.{u} R)) := by
    intro j
    have hmap : Submodule.map (e.toLinearEquiv.toLinearMap)
        (I ^ (j + 1) • (⊤ : Submodule R (limit D : ModuleCat.{u} R))) =
        I ^ (j + 1) • (⊤ : Submodule R (limit E : ModuleCat.{u} R)) := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr e.toLinearEquiv.surjective]
    rw [ModuleCat.hom_comp, LinearMap.ker_comp,
      Stacks.Coherent.moduleLimit_projection_ker E hE.surjective hE.ker hI j,
      ← Iso.toLinearMap_toLinearEquiv e, ← hmap,
      Submodule.comap_map_eq_of_injective e.toLinearEquiv.injective]
  -- both towers are the quotients of `limit D` by the powers of `I`
  set φ : ∀ j : ℕ, D.obj (op j) ≃ₗ[R] E.obj (op j) := fun j =>
    (LinearMap.quotKerEquivOfSurjective _ (hsD j)).symm.trans
      ((Submodule.quotEquivOfEq _ _ ((hkD j).trans (hkE j).symm)).trans
        (LinearMap.quotKerEquivOfSurjective _ (hsE j))) with hφdef
  have hφ : ∀ (j : ℕ) (w : (limit D : ModuleCat.{u} R)),
      φ j ((limit.π D (op j)).hom w) = (e.hom ≫ limit.π E (op j)).hom w := by
    intro j w
    have h1 : (LinearMap.quotKerEquivOfSurjective _ (hsD j)).symm
        ((limit.π D (op j)).hom w) = Submodule.Quotient.mk w :=
      (LinearMap.quotKerEquivOfSurjective _ (hsD j)).symm_apply_eq.2
        (LinearMap.quotKerEquivOfSurjective_apply_mk _ (hsD j) w).symm
    rw [hφdef]
    change LinearMap.quotKerEquivOfSurjective _ (hsE j)
        (Submodule.quotEquivOfEq _ _ ((hkD j).trans (hkE j).symm)
          ((LinearMap.quotKerEquivOfSurjective _ (hsD j)).symm
            ((limit.π D (op j)).hom w))) = _
    rw [h1]
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ (hsE j) w
  refine ⟨φ, fun j l h x => ?_⟩
  obtain ⟨w, rfl⟩ := hsD l x
  have hwD : tr D h ((limit.π D (op l)).hom w) = (limit.π D (op j)).hom w :=
    congrArg (fun ψ : (limit D : ModuleCat.{u} R) ⟶ D.obj (op j) => (ModuleCat.Hom.hom ψ) w)
      (limit.w D (homOfLE h).op)
  have h0 : (e.hom ≫ limit.π E (op l)) ≫ invTransition E h = e.hom ≫ limit.π E (op j) := by
    rw [Category.assoc, limit.w E (homOfLE h).op]
  have hwE : tr E h ((e.hom ≫ limit.π E (op l)).hom w) =
      (e.hom ≫ limit.π E (op j)).hom w :=
    congrArg (fun ψ : (limit D : ModuleCat.{u} R) ⟶ E.obj (op j) => (ModuleCat.Hom.hom ψ) w) h0
  rw [hφ l w, hwE, hwD, hφ j w]

/-! ### The graded system of sections on `U` -/

section Sections

open Stacks.ProObject

variable (S : AlgebraizationSituation.{u})
  {σ : Type v} [SetLike σ S.A] [AddSubgroupClass σ S.A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
  (ℳ : ∀ n : ℕ, ℤ → AddSubgroup (M.obj (op n)))
  [∀ n : ℕ, DirectSum.Decomposition (ℳ n)] [∀ n : ℕ, SetLike.GradedSMul 𝒜 (ℳ n)]
  {r : ℕ} (fgen : Fin r → S.A) (hspan : Ideal.span (Set.range fgen) = S.a)
  {cdeg : Fin r → ℕ}

/-- The inverse system `(Γ(U, M̃ₙ|U))` of sections on `U` of the system presenting the coherent
formal module. -/
private def sectionsSystem : ℕᵒᵖ ⥤ ModuleCat.{u} S.A :=
  (M ⋙ tilde.functor (.of S.A) ⋙ Scheme.Modules.restrictFunctor S.U.ι) ⋙
    (_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op ⊤) ⋙
      ModuleCat.restrictScalars (scalarMap S))

private theorem sectionsSystem_obj (n : ℕ) :
    (sectionsSystem S M).obj (op n) =
      complementGlobalSections S.A S.a (complementTilde S.A S.a (M.obj (op n))) :=
  rfl

/-- The grading of `Γ(U, M̃ₙ|U)` read off the graded Čech model. -/
private def sectionsGrading :
    ∀ n : ℕ, ℤ → AddSubgroup ((sectionsSystem S M).obj (op n)) :=
  fun n => complementPiece 𝒜 (ℳ n) fgen S.a hspan

/-- The grading of `Γ(U, M̃ₙ|U)` is a `DirectSum.Decomposition`. -/
@[instance_reducible] private def sectionsDecomposition (hcdeg : ∀ i, fgen i ∈ 𝒜 (cdeg i)) :
    ∀ n : ℕ, DirectSum.Decomposition (sectionsGrading S 𝒜 M ℳ fgen hspan n) :=
  fun n => complementDecomposition 𝒜 (ℳ n) fgen S.a hspan hcdeg

omit [∀ n : ℕ, DirectSum.Decomposition (ℳ n)] in
private theorem smul_mem_sectionsGrading (hcdeg : ∀ i, fgen i ∈ 𝒜 (cdeg i))
    (n i : ℕ) (d : ℤ) (a : S.A) (x : (sectionsSystem S M).obj (op n)) (ha : a ∈ 𝒜 i)
    (hx : x ∈ sectionsGrading S 𝒜 M ℳ fgen hspan n d) :
    a • x ∈ sectionsGrading S 𝒜 M ℳ fgen hspan n ((i : ℤ) + d) :=
  smul_mem_complementPiece 𝒜 (ℳ n) fgen S.a hspan hcdeg ha hx

/-- **The transitions of `(Γ(U, M̃ₙ|U))` preserve degrees.** -/
private theorem tr_mem_sectionsGrading (hcdeg : ∀ i, fgen i ∈ 𝒜 (cdeg i))
    (hahom : S.a.IsHomogeneous 𝒜)
    (hMtr : ∀ (n m : ℕ) (h : n ≤ m) (d : ℤ) (x : M.obj (op m)), x ∈ ℳ m d →
      tr M h x ∈ ℳ n d)
    (n m : ℕ) (h : n ≤ m) (d : ℤ) (x : (sectionsSystem S M).obj (op m))
    (hx : x ∈ sectionsGrading S 𝒜 M ℳ fgen hspan m d) :
    tr (sectionsSystem S M) h x ∈ sectionsGrading S 𝒜 M ℳ fgen hspan n d :=
  mem_complementPiece_of_comp_complementRes 𝒜 (ℳ m) (ℳ n) fgen S.a hspan hcdeg hahom
    (tr M h) (fun d' y hy => hMtr n m h d' y hy)
    (isIPowerTorsion_quotient_range_complementRes S (M.obj (op m)))
    (tr (sectionsSystem S M) h)
    (fun y => complementRes_naturality S (M.map (homOfLE h).op) y) hx

/-- The restriction maps `Mₙ → Γ(U, M̃ₙ|U)`, as a morphism of inverse systems. -/
private def sectionsRes : M ⟶ sectionsSystem S M where
  app n := ModuleCat.ofHom (X := (M.obj n : Type u))
    (Y := ((sectionsSystem S M).obj n : Type u)) (complementRes (M := M.obj n) S.a)
  naturality _ _ φ :=
    ModuleCat.hom_ext (LinearMap.ext fun x => (complementRes_naturality S (M.map φ) x).symm)

private theorem sectionsRes_app_hom (n : ℕᵒᵖ) :
    ((sectionsRes S M).app n).hom = complementRes (M := M.obj n) S.a := rfl

omit [∀ n : ℕ, DirectSum.Decomposition (ℳ n)] [∀ n : ℕ, SetLike.GradedSMul 𝒜 (ℳ n)] in
private theorem mem_sectionsGrading_sectionsRes (hcdeg : ∀ i, fgen i ∈ 𝒜 (cdeg i))
    (n : ℕ) (d : ℤ) (x : M.obj (op n)) (hx : x ∈ ℳ n d) :
    ((sectionsRes S M).app (op n)).hom x ∈ sectionsGrading S 𝒜 M ℳ fgen hspan n d := by
  rw [sectionsRes_app_hom]
  exact complementRes_mem_complementPiece 𝒜 (ℳ n) fgen S.a hspan hcdeg hx

private theorem isIPowerTorsion_ker_sectionsRes (n : ℕ) :
    IsIPowerTorsion S.A (LinearMap.ker ((sectionsRes S M).app (op n)).hom) S.a := by
  rw [sectionsRes_app_hom]
  exact isIPowerTorsion_ker_complementRes S (M.obj (op n))

private theorem isIPowerTorsion_quotient_range_sectionsRes (n : ℕ) :
    IsIPowerTorsion S.A
      ((sectionsSystem S M).obj (op n) ⧸
        LinearMap.range ((sectionsRes S M).app (op n)).hom) S.a := by
  rw [sectionsRes_app_hom]
  exact isIPowerTorsion_quotient_range_complementRes S (M.obj (op n))

/-- The sections of the presenting system are the sections of the coherent formal module. -/
private def sectionsSystemIso
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (eF : F.obj ≅ M ⋙ tilde.functor (.of S.A) ⋙ Scheme.Modules.restrictFunctor S.U.ι) :
    globalSectionsSystem S F ≅ sectionsSystem S M :=
  Functor.isoWhiskerRight eF _

private theorem idealPower_smul_top_sectionsSystem_eq_bot
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (eF : F.obj ≅ M ⋙ tilde.functor (.of S.A) ⋙ Scheme.Modules.restrictFunctor S.U.ι)
    (n : ℕ) :
    S.I ^ (n + 1) • (⊤ : Submodule S.A ((sectionsSystem S M).obj (op n))) = ⊥ := by
  set e := sectionsSystemIso S M F eF with he
  refine le_antisymm (Submodule.smul_le.2 fun a ha y _ => ?_) bot_le
  have hid : (e.hom.app (op n)).hom ((e.inv.app (op n)).hom y) = y :=
    congrArg (fun φ : (sectionsSystem S M).obj (op n) ⟶ (sectionsSystem S M).obj (op n) =>
      (ModuleCat.Hom.hom φ) y) (e.inv_hom_id_app (op n))
  rw [Submodule.mem_bot, ← hid, ← map_smul,
    idealPower_smul_globalSections_eq_zero S F n ha ((e.inv.app (op n)).hom y), map_zero]

end Sections

/-! ### The coherent module associated to a finite module, and its completion on `U` -/

/-- The terms of a coherent adic system on `X` are quasi-coherent, being coherent. -/
public theorem isQuasicoherent_extensionObj (S : AlgebraizationSituation.{u})
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) (n : ℕᵒᵖ) :
    (G.obj.obj n).IsQuasicoherent :=
  let : (G.obj.obj n).IsCoherent := G.property.1 n.unop
  isQuasicoherent_of_isCoherent (G.obj.obj n)

/-- **A coherent adic system on the affine `X` is the sheafification of its global sections.**
Every term is quasi-coherent, so the counit of the tilde-global-sections adjunction is an
isomorphism there, and the counit is a natural transformation. -/
public def extensionSectionsTildeIso (S : AlgebraizationSituation.{u})
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) :
    extensionSections S G ⋙ tilde.functor (.of S.A) ≅ G.obj :=
  NatIso.ofComponents
    (fun n => @Stacks.AlgebraicGeometry.AffineBaseChangeLocality.tildeΓIso _ (G.obj.obj n)
      (isQuasicoherent_extensionObj S G n))
    (fun f => Scheme.Modules.fromTildeΓNatTrans.naturality (G.obj.map f))

/-- The same identification restricted to `U`: the system `(Γ(X, 𝒢ₙ)^~|_U)` is the termwise
restriction of `(𝒢ₙ)`. -/
public def extensionSectionsRestrictedTildeIso (S : AlgebraizationSituation.{u})
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) :
    extensionSections S G ⋙ restrictedTildeFunctor S ≅
      G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι :=
  Functor.isoWhiskerRight (extensionSectionsTildeIso S G) (Scheme.Modules.restrictFunctor S.U.ι)

/-- **The coherent `𝒪_X`-module `N^~` associated to a finite `A`-module `N`.** Over a Noetherian
ring the sheafification of a finite module is coherent, by [Stacks, Tag 01XZ]. -/
public def tildeCoherentModule (S : AlgebraizationSituation.{u}) (N : ModuleCat.{u} S.A)
    (hN : Module.Finite S.A N) :
    AlgebraicGeometry.SheafOfModules.CoherentModules S.X.ringCatSheaf :=
  haveI := hN
  ⟨(tilde.functor (.of S.A)).obj N,
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
      (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_tilde (R := CommRingCat.of S.A) N)⟩

open Stacks.ProObject CategoryTheory.Limits in
/-- **Clause (b) of Stacks Project, Tag 0EL4, from an identification of the adic quotients.**
Let `N` be a finite `A`-module and `(Wⱼ)` an inverse system of `A`-modules whose sheafifications
restrict on `U` to `(ℱₙ)`. If the adic quotients `N/I^{j+1}N` are isomorphic to the `Wⱼ`
compatibly with the transition maps, then `(ℱₙ)` is the completion of `N^~|_U`. -/
public theorem nonempty_completionIso_of_adicQuotientsEquiv
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (N : ModuleCat.{u} S.A) (hNfin : Module.Finite S.A N)
    (W : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (eWF : W ⋙ restrictedTildeFunctor S ≅ F.obj)
    (θ : ∀ j : ℕ, (N ⧸ S.I ^ (j + 1) • (⊤ : Submodule S.A N)) ≃ₗ[S.A] W.obj (op j))
    (hθ : ∀ (j l : ℕ) (h : j ≤ l) (x : N),
      tr W h (θ l (Submodule.Quotient.mk x)) = θ j (Submodule.Quotient.mk x)) :
    Nonempty ((completionFunctor S.U.toScheme (idealOnOpen S)).obj
      (restrictCoherentModules S.U.ι (tildeCoherentModule S N hNfin)) ≅ F) := by
  classical
  set L := restrictedTildeFunctor S with hL
  set 𝒞 := restrictCoherentModules S.U.ι (tildeCoherentModule S N hNfin) with h𝒞
  set ϖ : ∀ j : ℕ, N ⟶ W.obj (op j) := fun j =>
    ModuleCat.ofHom ((θ j).toLinearMap.comp
      (S.I ^ (j + 1) • (⊤ : Submodule S.A N)).mkQ) with hϖ
  -- an isomorphism has torsion kernel and cokernel, both being trivial
  have hker : ∀ j : ℕ, IsIPowerTorsion S.A (LinearMap.ker ((θ j).toLinearMap)) S.a := fun j => by
    rw [LinearEquiv.ker]
    exact isIPowerTorsion_of_subsingleton _
  have hcoker : ∀ j : ℕ,
      IsIPowerTorsion S.A (W.obj (op j) ⧸ LinearMap.range ((θ j).toLinearMap)) S.a := fun j => by
    rw [LinearEquiv.range]
    exact isIPowerTorsion_of_subsingleton _
  -- the terms of the completion of `N^~|_U` are the sheafifications of the `N/I^{j+1}N`
  choose c hc using fun j : ℕ =>
    restrictedTilde_quotient_transition_idealPowerQuotient S N (W.obj (op j)) (j + 1)
      (θ j).toLinearMap ⟨hker j, hcoker j⟩
  have hqobj : ∀ j : ℕ, ((completionFunctor S.U.toScheme (idealOnOpen S)).obj 𝒞).obj.obj (op j) =
      idealPowerQuotient (idealOnOpen S) (j + 1) 𝒞.obj :=
    completionFunctor_obj S.U.toScheme (idealOnOpen S) 𝒞
  set cc : ∀ j : ℕ, ((completionFunctor S.U.toScheme (idealOnOpen S)).obj 𝒞).obj.obj (op j) ≅
      F.obj.obj (op j) := fun j =>
    eqToIso (hqobj j) ≪≫ c j ≪≫ eWF.app (op j) with hcc
  set Φ : ∀ j : ℕ, 𝒞.obj ⟶ F.obj.obj (op j) := fun j =>
    L.map (ϖ j) ≫ eWF.hom.app (op j) with hΦdef
  have hcΦ : ∀ j : ℕ,
      completionProjection S.U.toScheme (idealOnOpen S) 𝒞 j ≫ (cc j).hom = Φ j := by
    intro j
    have hinner : completionProjection S.U.toScheme (idealOnOpen S) 𝒞 j ≫ eqToHom (hqobj j) =
        cokernel.π (idealPowerMultiple (idealOnOpen S) (j + 1) 𝒞.obj).ι :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => cokernel.π (idealPowerMultiple (idealOnOpen S) (j + 1) 𝒞.obj).ι ≫ k)
            ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ ((c j).hom ≫ (eWF.app (op j)).hom)) hinner) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun k => k ≫ (eWF.app (op j)).hom) (hc j)
  have hΦ : ∀ {m n : ℕᵒᵖ} (f : m ⟶ n), Φ m.unop ≫ F.obj.map f = Φ n.unop := by
    intro m n f
    have hle : n.unop ≤ m.unop := leOfHom f.unop
    have hfeq : f = (homOfLE hle).op := Subsingleton.elim _ _
    have hstep : ϖ m.unop ≫ W.map f = ϖ n.unop := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change (W.map f).hom ((θ m.unop) (Submodule.Quotient.mk x)) = _
      rw [hfeq]
      exact hθ n.unop m.unop hle x
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => L.map (ϖ m.unop) ≫ k)
      (eWF.hom.naturality f).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ eWF.hom.app n) (L.map_comp _ _).symm) ?_
    exact congrArg (fun k => L.map k ≫ eWF.hom.app n) hstep
  exact ⟨ObjectProperty.isoMk _
    (completionIsoOfProjections S.U.toScheme (idealOnOpen S) 𝒞 F.obj Φ hΦ cc hcΦ)⟩

open Stacks.ProObject Stacks.ProObject.LadderData in
/-- **The graded system of sections on `U`.** Under the hypotheses of Stacks 0EL4 the inverse
system `(Γ(U, ℱₙ))` is an inverse system of graded `A`-modules with degree-preserving transitions,
each term annihilated by the matching power of `I`, and it receives the restriction maps from
`(Mₙ)` with `𝔞`-power torsion kernel and cokernel; and it is linked by a ladder to the system of
global sections of a coherent adic extension of `(ℱₙ)` to `Spec(A)`, which is an adic tower of
finite `A`-modules whose sheafifications restrict on `U` to `(ℱₙ)` again.

This is the whole geometric input of Stacks 0EL4; the rest of the proof is the graded algebra of
[Stacks, Tag 0EKC] run on this data. -/
private theorem exists_gradedSectionsData (S : AlgebraizationSituation.{u})
    {σ : Type v} [SetLike σ S.A] [AddSubgroupClass σ S.A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (hirr : S.a = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (ℳ : ∀ n : ℕ, ℤ → AddSubgroup (M.obj (op n)))
    [∀ n : ℕ, DirectSum.Decomposition (ℳ n)]
    (hℳ : ∀ (n i : ℕ) (d : ℤ) (a : S.A) (x : M.obj (op n)), a ∈ 𝒜 i → x ∈ ℳ n d →
      a • x ∈ ℳ n ((i : ℤ) + d))
    (hMtr : ∀ (n m : ℕ) (h : n ≤ m) (d : ℤ) (x : M.obj (op m)), x ∈ ℳ m d →
      tr M h x ∈ ℳ n d)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hpres : Nonempty (F.obj ≅
      M ⋙ tilde.functor (.of S.A) ⋙ Scheme.Modules.restrictFunctor S.U.ι))
    (hext : CanonicallyExtends S F) :
    ∃ (Hm : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (𝓗 : ∀ n : ℕ, ℤ → AddSubgroup (Hm.obj (op n)))
        (_ : ∀ n : ℕ, DirectSum.Decomposition (𝓗 n)) (ρ : M ⟶ Hm)
        (W : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (_ : ∀ j : ℕ, Module.Finite S.A (W.obj (op j)))
        (_ : LadderData Hm W),
      IsAdicTower S.I W ∧
      (∀ (n i : ℕ) (d : ℤ) (a : S.A) (x : Hm.obj (op n)), a ∈ 𝒜 i → x ∈ 𝓗 n d →
        a • x ∈ 𝓗 n ((i : ℤ) + d)) ∧
      (∀ (n m : ℕ) (h : n ≤ m) (d : ℤ) (x : Hm.obj (op m)), x ∈ 𝓗 m d →
        tr Hm h x ∈ 𝓗 n d) ∧
      (∀ n : ℕ, S.I ^ (n + 1) • (⊤ : Submodule S.A (Hm.obj (op n))) = ⊥) ∧
      (∀ (n : ℕ) (d : ℤ) (x : M.obj (op n)), x ∈ ℳ n d → (ρ.app (op n)).hom x ∈ 𝓗 n d) ∧
      (∀ n : ℕ, IsIPowerTorsion S.A (LinearMap.ker (ρ.app (op n)).hom) S.a) ∧
      (∀ n : ℕ, IsIPowerTorsion S.A
        (Hm.obj (op n) ⧸ LinearMap.range (ρ.app (op n)).hom) S.a) ∧
      Nonempty (W ⋙ restrictedTildeFunctor S ≅ F.obj) := by
  classical
  obtain ⟨eF⟩ := hpres
  obtain ⟨G, ⟨e⟩⟩ := hext
  have hlad := hasProLadder_of_proIso S F G e
  obtain ⟨eGF⟩ :=
    nonempty_restrictionIso_of_proIso S F (tildeGlobalSectionsPullbackIso S F) G e
  have hahom : S.a.IsHomogeneous 𝒜 := hirr ▸ (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous
  obtain ⟨r, fgen, cdeg, hcdeg, hspan⟩ :=
    Stacks.GradedLocalization.exists_fin_homogeneous_span 𝒜 hahom S.a.fg_of_isNoetherianRing
  let : ∀ n : ℕ, SetLike.GradedSMul 𝒜 (ℳ n) :=
    fun n => ⟨fun {_ _ _ _} ha hx => hℳ n _ _ _ _ ha hx⟩
  obtain ⟨L⟩ := exists_ladderData
    (HasProLadder.of_natIso (sectionsSystemIso S M F eF) hlad)
  exact ⟨sectionsSystem S M, sectionsGrading S 𝒜 M ℳ fgen hspan,
    sectionsDecomposition S 𝒜 M ℳ fgen hspan hcdeg, sectionsRes S M,
    extensionSections S G, finite_extensionSections S G, L,
    isAdicTower_extensionSections S G,
    smul_mem_sectionsGrading S 𝒜 M ℳ fgen hspan hcdeg,
    tr_mem_sectionsGrading S 𝒜 M ℳ fgen hspan hcdeg hahom hMtr,
    idealPower_smul_top_sectionsSystem_eq_bot S M F eF,
    mem_sectionsGrading_sectionsRes S 𝒜 M ℳ fgen hspan hcdeg,
    isIPowerTorsion_ker_sectionsRes S M,
    isIPowerTorsion_quotient_range_sectionsRes S M,
    ⟨extensionSectionsRestrictedTildeIso S G ≪≫ eGF⟩⟩

open Stacks.ProObject Stacks.ProObject.LadderData CategoryTheory.Limits in
/-- **The graded algebraization, with explicit witnesses.** In the algebraization situation of a
graded Noetherian ring `A` whose irrelevant ideal is `𝔞` and whose ideal `I` is homogeneous, let
`(ℱₙ)` be a coherent `I`-adic system on `U = Spec(A) ∖ V(𝔞)` presented by an inverse system
`(Mₙ)` of graded `A`-modules, and suppose `(ℱₙ)` extends canonically to `Spec(A)`. Then there is
a finite graded `A`-module `N` such that `(ℱₙ)` is the completion of the coherent module
associated to `N`, together with the data comparing `(N/Iⁿ⁺¹N)` with `(Mₙ)`: the inverse system
`(Hₙ) = (Γ(U, ℱₙ))` of graded `A`-modules, degree-preserving restriction maps `(Mₙ) → (Hₙ)`
with `𝔞`-power torsion kernel and cokernel, and a ladder of degree-preserving maps between `(Hₙ)`
and a graded inverse system identified with `(N/Iⁿ⁺¹N)`.

This is the engine of [Stacks, Tag 0EL4]; the tag itself, with clause (a) stated as a
pro-isomorphism in the category of graded modules modulo torsion, is
`Stacks.Algebraization.exists_finite_graded_proIso_completion_of_canonicallyExtends`.

Clause (b) comes from the same ladders read on limits. The graded adic tower built out of the
stable images of `(Hₙ)` and the system `(Γ(X, 𝒢ₙ))` of global sections of the canonical extension
are both adic towers and are linked by a chain of two ladders, so they have the same limit and
therefore the same terms; since `N/Iⁿ⁺¹N` is the tower's level `n`, this identifies `N/Iⁿ⁺¹N`
with `Γ(X, 𝒢ₙ)` compatibly with the transitions. Sheafifying and restricting to `U` turns that
into an identification of `(ℱₙ)` with the completion of `N^~|_U`, by
`Stacks.Algebraization.nonempty_completionIso_of_adicQuotientsEquiv`. -/
public theorem exists_finite_graded_ladder_of_canonicallyExtends
    (S : AlgebraizationSituation.{u})
    {σ : Type v} [SetLike σ S.A] [AddSubgroupClass σ S.A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (hirr : S.a = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (hIhom : S.I.IsHomogeneous 𝒜)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (ℳ : ∀ n : ℕ, ℤ → AddSubgroup (M.obj (op n)))
    [∀ n : ℕ, DirectSum.Decomposition (ℳ n)]
    (hℳ : ∀ (n i : ℕ) (d : ℤ) (a : S.A) (x : M.obj (op n)), a ∈ 𝒜 i → x ∈ ℳ n d →
      a • x ∈ ℳ n ((i : ℤ) + d))
    (hMtr : ∀ (n m : ℕ) (h : n ≤ m) (d : ℤ) (x : M.obj (op m)), x ∈ ℳ m d →
      tr M h x ∈ ℳ n d)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hpres : Nonempty (F.obj ≅
      M ⋙ tilde.functor (.of S.A) ⋙ Scheme.Modules.restrictFunctor S.U.ι))
    (hext : CanonicallyExtends S F) :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module S.A N) (𝒩 : ℤ → AddSubgroup N)
        (_ : DirectSum.Decomposition 𝒩) (hNfin : Module.Finite S.A N),
      (∀ (i : ℕ) (d : ℤ) (a : S.A) (x : N), a ∈ 𝒜 i → x ∈ 𝒩 d → a • x ∈ 𝒩 ((i : ℤ) + d)) ∧
      Nonempty ((completionFunctor S.U.toScheme (idealOnOpen S)).obj
          (restrictCoherentModules S.U.ι
            (tildeCoherentModule S (ModuleCat.of S.A N) hNfin)) ≅ F) ∧
      ∃ (Hm : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (𝓗 : ∀ n : ℕ, ℤ → AddSubgroup (Hm.obj (op n)))
          (_ : ∀ n : ℕ, DirectSum.Decomposition (𝓗 n))
          (Nsys : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
          (𝒩s : ∀ k : ℕ, ℤ → AddSubgroup (Nsys.obj (op k)))
          (ε : ∀ k : ℕ, (N ⧸ S.I ^ (k + 1) • (⊤ : Submodule S.A N)) ≃ₗ[S.A] Nsys.obj (op k))
          (ρ : M ⟶ Hm) (L : LadderData Nsys Hm),
        (∀ (n i : ℕ) (d : ℤ) (a : S.A) (x : Hm.obj (op n)), a ∈ 𝒜 i → x ∈ 𝓗 n d →
            a • x ∈ 𝓗 n ((i : ℤ) + d)) ∧
        (∀ (n m : ℕ) (h : n ≤ m) (d : ℤ) (x : Hm.obj (op m)), x ∈ 𝓗 m d →
            tr Hm h x ∈ 𝓗 n d) ∧
        (∀ (k : ℕ) (d : ℤ) (x : N), x ∈ 𝒩 d → ε k (Submodule.Quotient.mk x) ∈ 𝒩s k d) ∧
        (∀ (k : ℕ) (d : ℤ) (z : Nsys.obj (op k)), z ∈ 𝒩s k d →
            ∃ x ∈ 𝒩 d, ε k (Submodule.Quotient.mk x) = z) ∧
        (∀ (k l : ℕ) (h : k ≤ l) (x : N),
            tr Nsys h (ε l (Submodule.Quotient.mk x)) = ε k (Submodule.Quotient.mk x)) ∧
        (∀ (n : ℕ) (d : ℤ) (x : M.obj (op n)), x ∈ ℳ n d → (ρ.app (op n)).hom x ∈ 𝓗 n d) ∧
        (∀ n : ℕ, IsIPowerTorsion S.A (LinearMap.ker (ρ.app (op n)).hom) S.a) ∧
        (∀ n : ℕ, IsIPowerTorsion S.A
            (Hm.obj (op n) ⧸ LinearMap.range (ρ.app (op n)).hom) S.a) ∧
        (∀ (k : ℕ) (d : ℤ) (x : Nsys.obj (op (L.p k))), x ∈ 𝒩s (L.p k) d →
            (L.f k).hom x ∈ 𝓗 k d) ∧
        (∀ (n : ℕ) (d : ℤ) (x : Hm.obj (op (L.q n))), x ∈ 𝓗 (L.q n) d →
            (L.g n).hom x ∈ 𝒩s n d) := by
  classical
  obtain ⟨Hm, 𝓗, iH, ρ, W, hWfin, L, hW, hgr, hHtr, hHann, hρgr, hρker, hρcoker, ⟨eWF⟩⟩ :=
    exists_gradedSectionsData S hirr M ℳ hℳ hMtr F hpres hext
  have hIle : S.I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := hirr ▸ S.I_le_a
  have := hWfin
  have := iH
  -- the two reindexings supplied by the ladder
  choose m₁ hm₁le hm₁ using fun j => L.range_tr_eq_stable hW j
  choose m₀ hm₀ using fun k => L.mem_pow_smul_stable_of_tr_mem_pow_smul_top hW k
  have hm₁' : ∀ j m : ℕ, m₁ j ≤ m → ∀ h : j ≤ m,
      LinearMap.range (tr Hm h) = L.stable j := fun j m hjm h => hm₁ j m hjm h
  have hm₀' : ∀ (k m m' : ℕ), m₀ k ≤ m → ∀ h : m ≤ m', ∀ x : Hm.obj (op m'),
      x ∈ L.stable m' → tr Hm h x ∈ S.I ^ k • (⊤ : Submodule S.A (Hm.obj (op m))) →
        x ∈ S.I ^ k • L.stable m' := fun k m m' hk h x hx hxI => hm₀ k m m' hk h x hx hxI
  -- the graded adic tower
  have hfinT : ∀ k : ℕ, Module.Finite S.A (stableQuot (H := Hm) m₀ m₁ S.I k) :=
    fun k => finite_stableQuot m₀ m₁ S.I L hm₁' k
  let iT : ∀ k : ℕ, DirectSum.Decomposition (stableQuotPiece (H := Hm) m₀ m₁ S.I 𝓗 k) :=
    fun k => stableQuotDecomposition 𝒜 m₀ m₁ S.I 𝓗 hgr hHtr hIhom k
  -- the graded limit theorem of Stacks 0EKC
  obtain ⟨N, hNg, hNm, 𝒩, hNdec, fq, hNfin, hNgr, hfgr, hfsurj, hfker, hfcomp⟩ :=
    hIhom.exists_finite_graded_forall_ker_eq_pow_smul_top hIle
      (stableQuotPiece (H := Hm) m₀ m₁ S.I 𝓗)
      (fun k i d a x ha hx => smul_mem_stableQuotPiece 𝒜 m₀ m₁ S.I 𝓗 hgr k i d a x ha hx)
      (fun k => stableQuotTr (H := Hm) m₀ m₁ S.I k)
      (fun k d z hz => stableQuotTr_mem_stableQuotPiece m₀ m₁ S.I 𝓗 hHtr k d z hz)
      (fun k => surjective_stableQuotTr m₀ m₁ S.I L hm₁' k)
      (fun k => ker_stableQuotTr m₀ m₁ S.I L hm₁' hm₀' k)
  choose equot hequot using fun n =>
    exists_quotient_smul_top_equiv (S.I ^ n) (fq n) (hfsurj n) (hfker n)
  have hequottr : ∀ (k l : ℕ) (h : k ≤ l) (x : N),
      tr (stableQuotSystem (H := Hm) m₀ m₁ S.I) h (equot (l + 1) (Submodule.Quotient.mk x)) =
        equot (k + 1) (Submodule.Quotient.mk x) := by
    intro k l h x
    induction l, h using Nat.le_induction with
    | base => exact tr_self _ _ _
    | succ l hl ih =>
        have h2 : tr (stableQuotSystem (H := Hm) m₀ m₁ S.I) (Nat.le_succ l)
              (equot (l + 1 + 1) (Submodule.Quotient.mk x)) =
            equot (l + 1) (Submodule.Quotient.mk x) := by
          rw [tr_stableQuotSystem_succ, hequot, hequot]
          exact congrFun (congrArg DFunLike.coe (hfcomp (l + 1))) x
        refine (tr_tr (stableQuotSystem (H := Hm) m₀ m₁ S.I) hl (Nat.le_succ l)
          (equot (l + 1 + 1) (Submodule.Quotient.mk x))).symm.trans ?_
        rw [h2]
        exact ih
  -- clause (b): the adic quotients of `N` are the sections of the canonical extension
  have hlT : IsAdicTower S.I (stableQuotSystem (H := Hm) m₀ m₁ S.I) :=
    isAdicTower_stableQuotSystem m₀ m₁ S.I L hm₁' hm₀'
  obtain ⟨eLim1, -⟩ := exists_limitIso_of_hasProLadder (limit.cone Hm) (limit.isLimit Hm)
    (hasProLadder_stableQuotSystem m₀ m₁ S.I hHann)
  obtain ⟨eLim2, -⟩ := exists_limitIso_of_hasProLadder (limit.cone W) (limit.isLimit W)
    (show HasProLadder Hm W from ⟨L.p, L.f, L.q, L.g, L.cf, L.cg, L.fg, L.gf⟩)
  obtain ⟨φ, hφ⟩ := exists_linearEquiv_of_limitIso_isAdicTower S.I.fg_of_isNoetherianRing
    hlT hW (eLim1 ≪≫ eLim2)
  have hθ : ∀ (j l : ℕ) (h : j ≤ l) (x : N),
      tr W h ((equot (l + 1)).trans (φ l) (Submodule.Quotient.mk x)) =
        (equot (j + 1)).trans (φ j) (Submodule.Quotient.mk x) := by
    intro j l h x
    have key := hφ j l h
      (show ((stableQuotSystem (H := Hm) m₀ m₁ S.I).obj (op l) : Type u) from
        equot (l + 1) (Submodule.Quotient.mk x))
    exact key.trans (DFunLike.congr_arg (φ j) (hequottr j l h x))
  -- the comparison `(Mₙ) → (Hₙ)`
  refine ⟨N, hNg, hNm, 𝒩, hNdec, hNfin, hNgr,
    nonempty_completionIso_of_adicQuotientsEquiv S F (ModuleCat.of S.A N) hNfin W eWF
      (fun j => (equot (j + 1)).trans (φ j)) hθ,
    Hm, 𝓗, iH,
    stableQuotSystem (H := Hm) m₀ m₁ S.I,
    fun k => stableQuotPiece (H := Hm) m₀ m₁ S.I 𝓗 (k + 1),
    fun k => equot (k + 1),
    ρ,
    stableQuotLadderData m₀ m₁ S.I hHann,
    hgr, hHtr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun k d x hx => hequot (k + 1) x ▸ hfgr (k + 1) d x hx
  · intro k d z hz
    obtain ⟨x, hx, hxz⟩ := DirectSum.exists_mem_graded_eq_of_surjective 𝒩
      (stableQuotPiece (H := Hm) m₀ m₁ S.I 𝓗 (k + 1)) (fq (k + 1)).toAddMonoidHom
      (fun d' y hy => hfgr (k + 1) d' y hy) (hfsurj (k + 1)) hz
    exact ⟨x, hx, (hequot (k + 1) x).trans hxz⟩
  · exact hequottr
  · exact hρgr
  · exact hρker
  · exact hρcoker
  · exact fun k d x hx => stableQuotDown_mem m₀ m₁ S.I 𝓗 hHtr hHann k d x hx
  · exact fun n d x hx => Submodule.mkQ_mem_gradedQuotientPiece _ hx



/-! ### Stacks 0EL4 -/

section ProIso

open Stacks.ProObject CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

/-- **Stacks Project, Tag 0EL4.** In the algebraization situation (Situation 0EHC) let `A` be
graded with irrelevant ideal `𝔞 = A₊` and `I` homogeneous, let `(ℱₙ)` be an object of
`Coh(U, I𝒪_U)` presented as `(M̃ₙ|_U)` by an inverse system `(Mₙ)` of graded `A`-modules, and
suppose `(ℱₙ)` extends canonically to `X = Spec(A)`. Then there is a finite graded `A`-module `N`
such that

* (a) the inverse systems `(N/IⁿN)` and `(Mₙ)` are pro-isomorphic in the category of graded
  `A`-modules modulo `A₊`-power torsion modules, and
* (b) `(ℱₙ)` is the completion of the coherent module associated to `N`.

The category of graded `A`-modules modulo `A₊`-power torsion modules is the localization of
`GradedModuleCat` at the maps with `A₊`-power torsion kernel and cokernel
(`GradedModuleCat.isoModTorsion`), and the pro-objects of the two inverse systems composed with
the localization functor are presented as colimits of representables, as in
`Stacks.ProObject.hasProLadder`. The systems are indexed from `0`: the term `n` of `(Mₙ)` and of
`(ℱₙ)` is the source's term `n + 1`, and the term `n` of the adic quotients is `N/Iⁿ⁺¹N`
(`GradedModuleCat.adicQuotients`). The coherent module associated to `N` is restricted to `U`
before completing, `(ℱₙ)` living on `U`.

The restriction maps `Mₙ → Γ(U, ℱₙ)` become isomorphisms in the quotient category, and
`(Γ(U, ℱₙ))` is linked to `(N/Iⁿ⁺¹N)` by a ladder of degree-preserving maps
(`Stacks.Algebraization.exists_finite_graded_ladder_of_canonicallyExtends`), which is a
pro-isomorphism of graded modules (`Stacks.ProObject.nonempty_colimitYonedaIso_of_hasProLadder`)
and stays one after localizing. -/
@[stacks 0EL4]
public theorem exists_finite_graded_proIso_completion_of_canonicallyExtends
    (S : AlgebraizationSituation.{u})
    {σ : Type v} [SetLike σ S.A] [AddSubgroupClass σ S.A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (hirr : S.a = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (hIhom : S.I.IsHomogeneous 𝒜)
    (M : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, v} 𝒜)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hpres : Nonempty (F.obj ≅ M ⋙ GradedModuleCat.toModuleCat 𝒜 ⋙ tilde.functor (.of S.A) ⋙
      Scheme.Modules.restrictFunctor S.U.ι))
    (hext : CanonicallyExtends S F) :
    ∃ (N : GradedModuleCat.{u, u, v} 𝒜) (hN : Module.Finite S.A N.carrier),
      Nonempty (colimit ((GradedModuleCat.adicQuotients 𝒜 N S.I hIhom ⋙
          (GradedModuleCat.isoModTorsion 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal).Q).op ⋙
            yoneda) ≅
        colimit ((M ⋙
          (GradedModuleCat.isoModTorsion 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal).Q).op ⋙
            yoneda)) ∧
      Nonempty ((completionFunctor S.U.toScheme (idealOnOpen S)).obj
          (restrictCoherentModules S.U.ι
            (tildeCoherentModule S (ModuleCat.of S.A N.carrier) hN)) ≅ F) := by
  classical
  obtain ⟨N, hNg, hNm, 𝒩, hNdec, hNfin, hNgr, hcompl, Hm, 𝓗, iH, Nsys, 𝒩s, ε, ρ, L,
      hHgr, hHtr, hε, hε', hεtr, hρgr, hρker, hρcoker, hLf, hLg⟩ :=
    @exists_finite_graded_ladder_of_canonicallyExtends S σ _ _ 𝒜 _ hirr hIhom
      (M ⋙ GradedModuleCat.toModuleCat 𝒜) (fun n => (M.obj (op n)).grade)
      (fun n => (M.obj (op n)).decomposition)
      (fun n i d a x ha hx => GradedModuleCat.smul_mem_grade 𝒜 (M.obj (op n)) ha hx)
      (fun n m h d x hx => (M.map (homOfLE h).op).map_grade d x hx) F hpres hext
  let Ngr : GradedModuleCat.{u, u, v} 𝒜 := GradedModuleCat.ofGrading 𝒜 N 𝒩 hNgr
  let Hg : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, v} 𝒜 := GradedModuleCat.liftSystem 𝒜 Hm 𝓗 hHgr hHtr
  let Q := GradedModuleCat.adicQuotients 𝒜 Ngr S.I hIhom
  refine ⟨Ngr, hNfin, ?_, hcompl⟩
  -- the adic quotients of `N` are the system `Nsys`, as inverse systems of modules
  let eN : Q ⋙ GradedModuleCat.toModuleCat 𝒜 ≅ Nsys :=
    NatIso.ofComponents (fun k => (ε k.unop).toModuleIso) (fun {k l} φ => by
      refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
      rw [Subsingleton.elim φ (homOfLE (leOfHom φ.unop)).op]
      exact (hεtr l.unop k.unop (leOfHom φ.unop) x).symm)
  -- a ladder of degree-preserving maps between the adic quotients and `(Γ(U, ℱₙ))`
  have hlad : HasProLadder Q Hg := by
    refine GradedModuleCat.hasProLadder_of_toModuleCat 𝒜 (L.ofIsoLeft eN.symm) ?_ ?_
    · rintro k d _ ⟨x, hx, rfl⟩
      exact hLf k d _ (hε (L.p k) d x hx)
    · intro n d y hy
      obtain ⟨x, hx, hxz⟩ := hε' n d _ (hLg n d y hy)
      refine ⟨x, hx, ?_⟩
      change Submodule.Quotient.mk x = (ε n).symm ((L.g n).hom y)
      rw [← hxz, LinearEquiv.symm_apply_apply]
  -- the restriction maps `(Mₙ) → (Γ(U, ℱₙ))` are inverted in the quotient category
  let ρg : M ⟶ Hg :=
    { app := fun n => ⟨(ρ.app n).hom, fun d x hx => hρgr n.unop d x hx⟩
      naturality := fun _ _ f =>
        GradedModuleCat.hom_ext (congrArg ModuleCat.Hom.hom (ρ.naturality f)) }
  let W := GradedModuleCat.isoModTorsion 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  have hρW : ∀ n, W (ρg.app n) := fun n => by
    refine ⟨?_, ?_⟩ <;> rw [← hirr]
    exacts [hρker n.unop, hρcoker n.unop]
  have : ∀ n, IsIso ((Functor.whiskerRight ρg W.Q).app n) := fun n => W.Q_inverts _ (hρW n)
  have : IsIso (Functor.whiskerRight ρg W.Q) := NatIso.isIso_of_isIso_app _
  obtain ⟨eQH⟩ := nonempty_colimitYonedaIso_of_hasProLadder (hlad.map W.Q)
  exact ⟨eQH ≪≫ (colimitYonedaIsoOfNatIso (asIso (Functor.whiskerRight ρg W.Q))).symm⟩

end ProIso

end Stacks.Algebraization

end

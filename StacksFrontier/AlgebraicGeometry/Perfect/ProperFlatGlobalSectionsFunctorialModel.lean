module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseAlternatingCechBaseChangeCocycle
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsChainModel

/-!
# One finite projective complex computing the cohomology of every base change, functorially

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism of schemes and `F` a coherent
`𝒪_X`-module flat over `A`. [Stacks, Tag 07VL] asserts that there is a finite complex `M` of
finite projective `A`-modules with

`Hⁱ(X_{A'}, F_{A'}) = Hⁱ(M ⊗_A A')`  functorially in `A'`.

This file proves both halves of that assertion at once: the identification for every base change,
**as a family of isomorphisms** — a function of the ring map `φ : A ⟶ A'`, the cartesian square
exhibiting `X_{A'}` and the degree `i` — together with **its functoriality in `A'`**, the cocycle
square for a second base change `A' ⟶ A''`.

`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsUniversalModel.lean` and
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsUniversalModelData.lean` state the
first half alone; neither is changed here.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseChangeChainComparison`: the comparison
  `M ⊗_A A' ⟶ Č_alt(g⁻¹U, g^* F)` as a **morphism of complexes** of `A'`-modules — the termwise
  extension of scalars of the chain-level model `u : M ⟶ Č_alt(U, F)` of
  `exists_finiteProjectiveModel_quasiIso`, followed by the Čech base-change isomorphism of
  [Stacks, Tag 07VK] (2). Being a chain map rather than a morphism of the derived category, it
  has a composition law, and that is where the functoriality comes from.
* `…baseChangeChainComparisonHomologyIso`: the induced `Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')`.

## Main results

* `…quasiIso_baseChangeChainComparison`: the chain-level comparison is a quasi-isomorphism. Its
  first factor is one by `StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat` — both
  complexes are bounded above and termwise flat, the model's terms being projective and the Čech
  model's flat by [Stacks, Tag 01U4] — and its second factor is invertible.
* `…baseChangeChainComparison_comp`: **the cocycle square.** For a tower of two cartesian squares
  the comparison for the composite ring map is the composite of the two comparisons. This is
  `baseAlternatingCechComplexBaseChangeIso_comp` together with the naturality of
  `extendScalarsComplexCompIso` at the chain map `u`.
* `…exists_finiteProjectiveModel_homology_iso_functorial`: **[Stacks, Tag 07VL]**, both clauses.

## What the statement says

Under exactly the source's hypotheses — `A` Noetherian, `f` proper, `F` coherent and flat over
`A`, and nothing else — there exist a bounded complex `M` of finite projective `A`-modules, a
finite affine open cover of `X` with affine finite intersections, a family

`Θ(φ, square) : M ⊗_A A' ⟶ Č_alt(g⁻¹U, g^* F)`

of chain-level comparisons and a family

`c(φ, square, i) : Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')`

of identifications, such that every `Θ(φ, square)` is a quasi-isomorphism, each `c(φ, square, i)`
is the identification that `Θ(φ, square)` induces on homology — which is what makes the family
one family and not a choice per `A'` — and the comparisons satisfy the cocycle square: for
`ψ : A' ⟶ A''` and a second cartesian square,

`(Θ(φ) ⊗_{A'} A'') ∘ (base change of the Čech model along ψ) = Θ(ψ ∘ φ)`

read through `(M ⊗_A A') ⊗_{A'} A'' ≅ M ⊗_A A''`. That square is the functoriality in `A'`.

The cover is **not** a hypothesis: properness supplies one through
`exists_finiteAffineCover_of_isProper`, and it is bound inside the existential, so the statement
is about the morphism and not about a choice of cover.

**The source's closing citation.** [Stacks, Tag 07VL] ends by observing that flatness of `F` over
`A` is essential, with a reference to Hartshorne. That sentence has been ruled remark-level: it
is a citation to the literature rather than a clause owing a theorem, and it is recorded here as
documentation only. Flatness does enter everything above as a hypothesis of the source, and it is
what makes the base-change comparison of [Stacks, Tag 07VK] (2) invertible.

## Implementation notes

`Hⁱ(X', g^* F)` is spelled as the `i`-th homology of `RΓ(X', g^* F)` read in `D(A')`, as in
`ProperFlatGlobalSectionsUniversalModel.lean`, and the right-hand side is the homology of the
honest complex `M ⊗_A A'` of `A'`-modules.

The cover's index type carries a `LinearOrder` — the alternating Čech complex needs one — and so
is bound as data inside the existential; its finiteness is bound as the `Prop`-valued `Finite`.
Both are produced by `exists_finiteAffineCover_of_isProper`, which is what the proof instantiates
them with, so no binder of the statement is without an inhabitant.

Separatedness is never assumed: `IsProper` extends it, which is how
`exists_finiteAffineCover_of_isProper` and `isPerfect_derivedGlobalSections` get it here too, and
the base change of a separated morphism is separated by `isSeparated_of_isPullback`.
Quasi-coherence is likewise not assumed: it follows from coherence by
`isQuasicoherent_of_isCoherent`, seated in the statement by a `haveI`.

The whole file runs under `HasDerivedCategory.standard` at priority `10000`, as
`ProperFlatGlobalSections.lean` does; results proved under a different choice of derived-category
model do not unify with those.

## References

* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 06XY](https://stacks.math.columbia.edu/tag/06XY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

section Comparison

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] {f' : X' ⟶ Spec (.of A')}
  {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I]
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {M : CochainComplex (ModuleCat.{u} A) ℤ} (u : M ⟶ baseAlternatingCechComplex f U hU F)

/-- **The chain-level comparison `M ⊗_A A' ⟶ Č_alt(g⁻¹U, g^* F)`.** Extend the scalars of the
chain map `u : M ⟶ Č_alt(U, F)` termwise along `φ`, then apply the Čech base-change isomorphism
of [Stacks, Tag 07VK] (2).

Everything the remark's functoriality needs is visible here: this is a morphism of *complexes*,
so it has a composition law in the base ring, which `baseChangeChainComparison_comp` records. -/
def baseChangeChainComparison :
    extendScalarsComplex φ M ⟶ baseAlternatingCechComplex f' (fun j => g ⁻¹ᵁ U j)
      (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F) :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫
    (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff).hom

/-- The chain-level comparison is the extension of scalars of `u` followed by the Čech
base-change isomorphism. -/
theorem baseChangeChainComparison_eq :
    baseChangeChainComparison φ hsq F U hU hUaff u =
      ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫
        (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff).hom :=
  rfl

/-- **The chain-level comparison is a quasi-isomorphism.** Its first factor is one because `u` is
and because both complexes are bounded above with flat terms — the model's terms are projective,
hence flat, and the Čech model's are flat by [Stacks, Tag 01U4] in the form
`flat_baseAlternatingCechComplex_X` — so
`StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat` applies; its second factor is an
isomorphism. -/
theorem quasiIso_baseChangeChainComparison [Fintype I] [QuasiIso u]
    [∀ n : ℤ, Module.Flat A (M.X n)]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (b : ℤ) [M.IsStrictlyLE b] :
    QuasiIso (baseChangeChainComparison φ hsq F U hU hUaff u) := by
  have : ∀ n : ℤ, Module.Flat A ((baseAlternatingCechComplex f U hU F).X n) :=
    flat_baseAlternatingCechComplex_X f U hU F hUaff hflat
  have h1 : QuasiIso (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) :=
    StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat φ b (Fintype.card I : ℤ) u
  refine (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 ?_
  rw [baseChangeChainComparison_eq, Functor.map_comp]
  infer_instance

/-- **The derived comparison `Q (M ⊗_A A') ⟶ RΓ(X', g^* F)` is an isomorphism.** It is the
localization of the chain-level comparison, which is a quasi-isomorphism, followed by the
identification of the Čech model of the inverse-image cover with `RΓ(X', g^* F)`. -/
theorem isIso_baseChangeChainComparisonDerived [Fintype I] [LinearOrder I] [QuasiIso u]
    [∀ n : ℤ, Module.Flat A (M.X n)]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (b : ℤ) [M.IsStrictlyLE b] :
    IsIso (DerivedCategory.Q.map (baseChangeChainComparison φ hsq F U hU hUaff u) ≫
      (alternatingCechIsoDerivedGlobalSectionsOverBase f' (fun j => g ⁻¹ᵁ U j)
        (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)
        (iInf_preimage_isAffineOpen φ hsq U hUaff)).hom) := by
  have := quasiIso_baseChangeChainComparison φ hsq F U hU hUaff u hflat b
  infer_instance

/-- **The identification `Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')`.** The derived comparison of
`isIso_baseChangeChainComparisonDerived`, read through the homology functor of `D(A')` and
through `DerivedCategory.homologyFunctorFactors`, which identifies the homology of `Q K` with the
homology of `K`. -/
def baseChangeChainComparisonHomologyIso [Fintype I] [LinearOrder I] [QuasiIso u]
    [∀ n : ℤ, Module.Flat A (M.X n)]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (b : ℤ) [M.IsStrictlyLE b] (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj
        (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F)) ≅
      (extendScalarsComplex φ M).homology i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map (baseChangeChainComparison φ hsq F U hU hUaff u) ≫
          (alternatingCechIsoDerivedGlobalSectionsOverBase f' (fun j => g ⁻¹ᵁ U j)
            (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)
            (iInf_preimage_isAffineOpen φ hsq U hUaff)).hom)
        (isIso_baseChangeChainComparisonDerived φ hsq F U hU hUaff u hflat b)).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A') i).app (extendScalarsComplex φ M)

/-- **The identification is the one the chain-level comparison induces.** Its inverse is the
homology of the derived comparison, read through `DerivedCategory.homologyFunctorFactors`. This
is what pins the family of identifications to the single chain map `u` over `A`. -/
theorem baseChangeChainComparisonHomologyIso_inv [Fintype I] [LinearOrder I] [QuasiIso u]
    [∀ n : ℤ, Module.Flat A (M.X n)]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (b : ℤ) [M.IsStrictlyLE b] (i : ℤ) :
    (baseChangeChainComparisonHomologyIso φ hsq F U hU hUaff u hflat b i).inv =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A') i).inv.app
          (extendScalarsComplex φ M) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).map
          (DerivedCategory.Q.map (baseChangeChainComparison φ hsq F U hU hUaff u) ≫
            (alternatingCechIsoDerivedGlobalSectionsOverBase f' (fun j => g ⁻¹ᵁ U j)
              (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)
              (iInf_preimage_isAffineOpen φ hsq U hUaff)).hom) :=
  rfl

end Comparison

section Cocycle

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  (φ : A →+* A') (ψ : A' →+* A'')
  {X X' X'' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f]
  {f' : X' ⟶ Spec (.of A')} {f'' : X'' ⟶ Spec (.of A'')}
  {g : X' ⟶ X} {g' : X'' ⟶ X'}
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (hsq' : IsPullback g' f'' f' (Spec.map (CommRingCat.ofHom ψ)))
  (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I]
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {M : CochainComplex (ModuleCat.{u} A) ℤ} (u : M ⟶ baseAlternatingCechComplex f U hU F)

/-- **The cocycle square: the chain-level comparison is functorial in the base ring.** For a
tower of two cartesian squares, extending the scalars along `ψ` of the comparison for `φ`,
following it by the Čech base-change isomorphism for `ψ` and then identifying the model of
`g'^* (g^* F)` with that of `(g' ≫ g)^* F`, gives the comparison for `ψ ∘ φ` and `g' ≫ g`, read
through the composition isomorphism `(M ⊗_A A') ⊗_{A'} A'' ≅ M ⊗_A A''`.

This is the functoriality in `A'` of [Stacks, Tag 07VL]. Its two ingredients are
`baseAlternatingCechComplexBaseChangeIso_comp`, the cocycle identity for the Čech base-change
isomorphism, and the naturality of `extendScalarsComplexCompIso` at the chain map `u` — which is
available because `u` is a chain map and not merely a morphism of the derived category. -/
theorem baseChangeChainComparison_comp :
    haveI : IsSeparated f' := isSeparated_of_isPullback φ hsq
    ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (baseChangeChainComparison φ hsq F U hU hUaff u) ≫
        (baseAlternatingCechComplexBaseChangeIso ψ hsq' ((Scheme.Modules.pullback g).obj F)
            (fun j => g ⁻¹ᵁ U j) (top_eq_iSup_preimage g U hU)
            (isAffineOpen_preimage φ hsq U hUaff)).hom ≫
        (baseAlternatingCechComplexMapIso f'' (fun j => (g' ≫ g) ⁻¹ᵁ U j)
          (top_eq_iSup_preimage (g' ≫ g) U hU)
          ((Scheme.Modules.pullbackComp g' g).app F)).hom =
      (extendScalarsComplexCompIso φ ψ).hom.app M ≫
        baseChangeChainComparison (ψ.comp φ)
          (Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g g' hsq hsq') F U hU hUaff u := by
  have : IsSeparated f' := isSeparated_of_isPullback φ hsq
  have hcoc : ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff).hom ≫
          (baseAlternatingCechComplexBaseChangeIso ψ hsq' ((Scheme.Modules.pullback g).obj F)
              (fun j => g ⁻¹ᵁ U j) (top_eq_iSup_preimage g U hU)
              (isAffineOpen_preimage φ hsq U hUaff)).hom ≫
          (baseAlternatingCechComplexMapIso f'' (fun j => (g' ≫ g) ⁻¹ᵁ U j)
            (top_eq_iSup_preimage (g' ≫ g) U hU)
            ((Scheme.Modules.pullbackComp g' g).app F)).hom =
        (extendScalarsComplexCompIso φ ψ).hom.app (baseAlternatingCechComplex f U hU F) ≫
          (baseAlternatingCechComplexBaseChangeIso (ψ.comp φ)
            (Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g g' hsq hsq')
            F U hU hUaff).hom :=
    baseAlternatingCechComplexBaseChangeIso_comp φ ψ hsq hsq' F U hU hUaff
  have hnatu : ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
              (ComplexShape.up ℤ)).map u) ≫
          (extendScalarsComplexCompIso φ ψ).hom.app (baseAlternatingCechComplex f U hU F) =
        (extendScalarsComplexCompIso φ ψ).hom.app M ≫
          ((ModuleCat.extendScalars.{u, u, u} (ψ.comp φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u :=
    (extendScalarsComplexCompIso φ ψ).hom.naturality u
  rw [baseChangeChainComparison_eq, baseChangeChainComparison_eq, Functor.map_comp,
    Category.assoc, hcoc, ← Category.assoc, ← Category.assoc, hnatu]

end Cocycle

section Carrier

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules)

/-- **[Stacks, Tag 07VL], Remark 30.22.2, both clauses.** Let `A` be a Noetherian ring,
`f : X ⟶ Spec A` a proper morphism of schemes and `F` a coherent `𝒪_X`-module flat over `A`. Then
there is a bounded complex `M` of finite projective `A`-modules, a finite affine open cover of `X`
whose finite intersections are affine, and a family of chain-level comparisons

`Θ(φ, square) : M ⊗_A A' ⟶ Č_alt(g⁻¹U, g^* F)`

indexed by a ring map `φ : A ⟶ A'` and a cartesian square exhibiting `X'` as the base change of
`X` along `Spec A' ⟶ Spec A`, together with a family of identifications

`c(φ, square, i) : Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')`

indexed also by the degree, such that

* every `Θ(φ, square)` is a quasi-isomorphism;
* `c(φ, square, i)` is the identification `Θ(φ, square)` induces on homology, so the family has a
  single origin over `A` and is not a choice per `A'`;
* **the comparisons are functorial in `A'`**: for a second ring map `ψ : A' ⟶ A''` and a second
  cartesian square, the extension of scalars along `ψ` of `Θ(φ, square)`, followed by the Čech
  base-change isomorphism for `ψ` and by the identification of the model of `g'^* (g^* F)` with
  that of `(g' ≫ g)^* F`, is `Θ(ψ ∘ φ, pasted square)` read through
  `(M ⊗_A A') ⊗_{A'} A'' ≅ M ⊗_A A''`.

The conditions are exactly the source's. Separatedness and quasi-coherence follow:
properness gives the first and coherence the second. The cover is not an input either — it is
bound inside the existential and produced by `exists_finiteAffineCover_of_isProper` — so the
statement is about `f` and `F` alone.

The source's closing sentence, that flatness of `F` over `A` is essential with a reference to
Hartshorne, has been ruled remark-level: it is a citation rather than a clause owing a theorem,
and the module docstring records it as such. -/
@[stacks 07VL "Remark 30.22.2 in full: one bounded complex M of finite projective A-modules, the \
identification H^i(X_{A'}, F_{A'}) = H^i(M ⊗_A A') for every base change given as a family of \
isomorphisms indexed by the ring map, the cartesian square and the degree and pinned to the \
single chain-level model over A, and the functoriality in A' as the cocycle square for a second \
base change A' ⟶ A''; under exactly the source's conditions — A Noetherian, f proper, F coherent \
and flat over A — with the finite affine cover bound inside the existential and supplied by \
properness. The closing citation to Hartshorne that flatness is essential is remark-level and \
appears as documentation in the module docstring."]
theorem exists_finiteProjectiveModel_homology_iso_functorial [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    haveI : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
    ∃ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite A (M.X i)) ∧ (∀ i : ℤ, Module.Projective A (M.X i)) ∧
        ∃ (I : Type u) (hIfin : Finite I) (hIlin : LinearOrder I) (U : I → X.Opens)
          (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i)),
          haveI : Finite I := hIfin
          letI : LinearOrder I := hIlin
          ∃ (_haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
            (Θ : ∀ {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
                {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X},
                IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)) →
                  (extendScalarsComplex φ M ⟶
                    baseAlternatingCechComplex f' (fun j => g ⁻¹ᵁ U j)
                      (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)))
            (c : ∀ {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
                {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
                (_hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) (i : ℤ),
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj
                    (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F)) ≅
                  (extendScalarsComplex φ M).homology i)),
            (∀ {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
                {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
                (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))),
                QuasiIso (Θ φ hsq)) ∧
              (∀ {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
                  {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
                  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) (i : ℤ),
                  (c φ hsq i).inv =
                    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A') i).inv.app
                        (extendScalarsComplex φ M) ≫
                      (DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).map
                        (DerivedCategory.Q.map (Θ φ hsq) ≫
                          (alternatingCechIsoDerivedGlobalSectionsOverBase f'
                            (fun j => g ⁻¹ᵁ U j) (top_eq_iSup_preimage g U hU)
                            ((Scheme.Modules.pullback g).obj F)
                            (iInf_preimage_isAffineOpen φ hsq U hUaff)).hom)) ∧
              (∀ {A' A'' : Type u} [CommRing A'] [CommRing A''] (φ : A →+* A') (ψ : A' →+* A'')
                  {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of A')} {f'' : X'' ⟶ Spec (.of A'')}
                  {g : X' ⟶ X} {g' : X'' ⟶ X'}
                  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
                  (hsq' : IsPullback g' f'' f' (Spec.map (CommRingCat.ofHom ψ))),
                  haveI : IsSeparated f' := isSeparated_of_isPullback φ hsq
                  ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
                          (ComplexShape.up ℤ)).map (Θ φ hsq) ≫
                      (baseAlternatingCechComplexBaseChangeIso ψ hsq'
                          ((Scheme.Modules.pullback g).obj F) (fun j => g ⁻¹ᵁ U j)
                          (top_eq_iSup_preimage g U hU)
                          (isAffineOpen_preimage φ hsq U hUaff)).hom ≫
                      (baseAlternatingCechComplexMapIso f'' (fun j => (g' ≫ g) ⁻¹ᵁ U j)
                        (top_eq_iSup_preimage (g' ≫ g) U hU)
                        ((Scheme.Modules.pullbackComp g' g).app F)).hom =
                    (extendScalarsComplexCompIso φ ψ).hom.app M ≫
                      Θ (ψ.comp φ)
                        (Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g g' hsq hsq')) := by
  classical
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨I, hIfin, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, u, hu⟩ :=
    exists_finiteProjectiveModel_quasiIso f U hU F haff hflat
  have : M.IsStrictlyLE b := hLE
  have := hu
  have : ∀ n : ℤ, Module.Flat A (M.X n) := fun n =>
    have := hproj n
    Module.Flat.of_projective
  exact ⟨M, a, b, hGE, hLE, hfin, hproj, I, Finite.of_fintype I, hIlin, U, hU, hUaff, haff,
    fun {A'} [CommRing A'] φ {X'} {f'} {g} hsq =>
      baseChangeChainComparison φ hsq F U hU hUaff u,
    fun {A'} [CommRing A'] φ {X'} {f'} {g} hsq i =>
      baseChangeChainComparisonHomologyIso φ hsq F U hU hUaff u hflat b i,
    fun {A'} [CommRing A'] φ {X'} {f'} {g} hsq =>
      quasiIso_baseChangeChainComparison φ hsq F U hU hUaff u hflat b,
    fun {A'} [CommRing A'] φ {X'} {f'} {g} hsq i =>
      baseChangeChainComparisonHomologyIso_inv φ hsq F U hU hUaff u hflat b i,
    fun {A'} {A''} [CommRing A'] [CommRing A''] φ ψ {X'} {X''} {f'} {f''} {g} {g'} hsq hsq' =>
      baseChangeChainComparison_comp φ ψ hsq hsq' F U hU hUaff u⟩

end Carrier

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end

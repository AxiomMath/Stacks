module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineIso

/-!
# The canonical map of Stacks 0D0I

Let `f : X ⟶ Y` be a morphism of schemes, let `U` be an open of `Y` and `V` an open of `X` with
`V ⊆ f^{-1}U`, and write `R = Γ(Y, U)` and `A = Γ(X, V)`.  This file builds the canonical map of
complexes of sheaves of `𝒪_V`-modules

`(NL_{A/R})~ ⟶ NL_{X/Y}|_V`

of Stacks 0D0I: the map adjoint, under the mapping property of the sheaf associated to a module
(Stacks 01BH, clause (4)), to the comparison on sections
`Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison`.

## Main definitions

* `Stacks.NaiveCotangentAffineMap.restrictTop` is the restriction of sections from `V` to
  `V.ι ''ᵁ ⊤`, as a map of `Γ(X, V)`-modules into the global sections over `V` of the restriction
  of a sheaf of `𝒪_X`-modules along the open immersion `V.ι`.  This is the semilinear datum the
  adjoint of Stacks 01BH consumes.
* `Stacks.NaiveCotangentAffineMap.descDouble` is the map out of a two-term complex of associated
  sheaves given by the adjoints of two maps into global sections.
* `Stacks.NaiveCotangentAffineMap.wholeStepMap` is the two previous items combined: for a complex
  `N` of sheaves of `𝒪_X`-modules concentrated in degrees `-1` and `0`, and maps of `Γ(X, V)`
  modules into the sections of its two terms over `V` commuting with its differential, the map
  from the associated two-term complex into `N|_V`.
* `Stacks.NaiveCotangentAffineMap.comparisonMap` is the canonical map of Stacks 0D0I.

## Main results

* `Stacks.NaiveCotangentAffineMap.sectionsLeg_comm`: the two identifications of the sections of
  the terms of `NL_{B/A}` with the two terms of
  `Stacks.SheafOfModules.naiveCotangentSections` carry the differential of the latter to the
  sections of the differential of the former.
* `Stacks.NaiveCotangentAffineMap.descDatum_comm`: the comparison on sections of
  `Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison`, read into the sections of
  `NL_{X/Y}` over `V`, commutes with the differentials.  This is the hypothesis
  `Stacks.NaiveCotangentAffineMap.wholeStepMap` is applied at.
* `Stacks.NaiveCotangentAffineMap.descDouble_f_negOne`,
  `Stacks.NaiveCotangentAffineMap.descDouble_f_zero`,
  `Stacks.NaiveCotangentAffineMap.wholeStepMap_f_negOne` and
  `Stacks.NaiveCotangentAffineMap.wholeStepMap_f_zero` identify the two nonzero components of
  the map out of a two-term complex of associated sheaves as the two adjoints it was built
  from.  They are the shape in which a stalkwise argument about the canonical map consumes it,
  `Stacks.AssociatedSheaf.stalkMap_associatedSheafDesc_germ_tmul` computing the germ of an
  adjoint.  They are stated over abstract data only: at the concrete presentation the same
  statements cost more than 200000 heartbeats, so a consumer should instantiate them rather than
  restate them.

## Implementation notes

**The unit of abstraction is the whole step.**  The sheaves of modules whose sections occur here
are sheafifications — the conormal sheaf and the tensor-differentials sheaf of the canonical
presentation of `𝒪_X` over `f^{-1}𝒪_Y` — and a definitional unfolding at them exhausts the
elaborator's budget: checking that the degree `-1` term of
`Stacks.SheafOfModules.naiveCotangentSections` is the sections of the degree `-1` term of
`NL_{X/Y}` costs more than 200000 heartbeats when the concrete presentation is substituted,
whereas the same check over abstract sheaves of rings costs about 3000.  Every statement here is
therefore made over abstract data — an abstract sheaf of modules on an open for the restriction
of sections, an abstract morphism of sheaves of rings on an abstract site for the two
identifications, an abstract ringed space for the adjoint — and the concrete presentation is
substituted only in the final section, where every declaration is a single application of one of
them.  No statement spells the concrete presentation out, and no proof unfolds it.

**Two readings of the section ring.**  `Γ(X, V)` is `X.presheaf.obj (op V)` and the site-level
comparison is stated over `X.sheaf.obj.obj (op V)`; the two are the same term, but instance
search does not pass between them, so a module over one of them is not found as a module over the
other.  The sections of `NL_{X/Y}` resolve only in the first reading and the two terms of
`Stacks.SheafOfModules.naiveCotangentSections` only in the second.  The two categories
`ModuleCat Γ(X, V)` and `ModuleCat ↑(X.sheaf.obj.obj (op V))` are nevertheless equal by `rfl`, so
a morphism whose source is written in one reading and whose target is written in the other
elaborates; `Stacks.NaiveCotangentAffineMap.sectionsLegNegOne` is where that happens, and it is
the only place a reading is crossed.  `Stacks.NaiveCotangentAffineMap.ofHomTo` exists for the
same reason: it takes its target as an object of `ModuleCat`, so that no instance has to be
synthesised for a carrier obtained by unfolding a functor.

**What is not here.**  That the canonical map is an isomorphism in `D(𝒪_V)` is not proved, and no
declaration in this file carries the tag 0D0I.  What is missing is the identification of its
germ: by `Stacks.AssociatedSheaf.stalkMap_associatedSheafDesc_germ_tmul` the stalk at `x` of
`Stacks.NaiveCotangentAffineMap.comparisonMap` sends `germ_x(s) ⊗ m` to
`germ_x(s) • germ_x(g(m))`, and the germ formulas of
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGerm`,
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGermTensor` and
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineIso` identify `germ_x(g(m))` with the
image of `m` under `Stacks.NaiveCotangentAffineComparison.canonicalStalkHom`; what that leaves is
the transport of those formulas along
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` and the comparison of the two actions of
the stalk of `𝒪_X` on the stalk of a term of `NL_{X/Y}`.  With those,
`Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom`,
`CochainComplex.quasiIso_of_isZero_X_of_addEquiv` and
`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso` give the tag.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is a
  step.
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (4): the mapping
  property of the sheaf associated to a module.
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a morphism of sheaves of rings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineMap

open Stacks.AssociatedSheaf Stacks.NaiveCotangentAffineIso
open Stacks.SheafOfModules Stacks.Sites.Conormal

/-! ### A morphism of modules into a given object -/

/-- **A linear map into the carrier of an object of `ModuleCat R`, as a morphism of that
category.**  `ModuleCat.ofHom` takes its target to be `ModuleCat.of R N` for a type `N`, so using
it where the target is an object produced by a functor makes the elaborator unfold that functor
and then search for a module structure on the result; here the target is an object, whose module
structure is one of its fields. -/
def ofHomTo {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M]
    (N : ModuleCat.{u} R) (φ : M →ₗ[R] N) : ModuleCat.of R M ⟶ N :=
  ModuleCat.ofHom φ

/-- `Stacks.NaiveCotangentAffineMap.ofHomTo` is the map it was built from. -/
theorem ofHomTo_apply {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M]
    (N : ModuleCat.{u} R) (φ : M →ₗ[R] N) (m : M) : ofHomTo N φ m = φ m := rfl

/-! ### Restriction of sections to the top open of an open subscheme -/

section Restrict

variable {X : Scheme.{u}} (V : X.Opens)

/-- **The structural map of the associated sheaf on `V` is the restriction map.**  The component
over the whole space of `Stacks.AssociatedSheaf.globalSectionsMap` for the ring map
`Stacks.NaiveCotangentAffineIso.alpha` is the restriction map of `𝒪_X` along
`V.ι ''ᵁ ⊤ = V`: that component is `alpha` followed by the restriction from `⊤` to `⊤`, which is
the identity, and `alpha` is itself that restriction map by
`AlgebraicGeometry.Scheme.Opens.topIso_inv`. -/
theorem globalSectionsMap_app_top_alpha (s : Γ(X, V)) :
    ((globalSectionsMap V.toScheme.toRingedSpace (alpha (V := V))).app (op ⊤)) s =
      (show ToType (V.toScheme.toRingedSpace.presheaf.obj (op ⊤)) from
        (X.presheaf.map (eqToHom V.ι_image_top).op) s) := by
  rw [globalSectionsMap_app]
  change (V.toScheme.presheaf.map (homOfLE le_top).op).hom (alpha s) = _
  rw [show (homOfLE (le_top (a := (⊤ : V.toScheme.Opens)))).op = 𝟙 (op ⊤) from rfl,
    V.toScheme.presheaf.map_id]
  change alpha s = _
  rw [alpha, Scheme.Opens.topIso_inv]
  rfl

variable (𝒩 : X.Modules)

/-- **The global sections over `V` of the restriction of `𝒩` along `V.ι`**, as a module over
`Γ(X, V)` through `Stacks.NaiveCotangentAffineIso.alpha`.  This is the target of the datum that
`Stacks.AssociatedSheaf.associatedSheafDesc` consumes. -/
def restrictGlobal : ModuleCat.{u} Γ(X, V) :=
  (globalSectionsFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).obj
    ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩)

/-- **The action of `Γ(X, V)` on the global sections of the restriction is the action of `𝒪_X` on
the sections over `V.ι ''ᵁ ⊤`.**  Scalars act on
`Stacks.NaiveCotangentAffineMap.restrictGlobal` through
`Stacks.AssociatedSheaf.globalSectionsMap` and then through the identification
`AlgebraicGeometry.Scheme.Hom.appIso` of the sections of `𝒪_V` with those of `𝒪_X`, which is the
identity for an open immersion of the form `V.ι`. -/
theorem smul_restrictGlobal (s : Γ(X, V)) (z : Γ(𝒩, V.ι ''ᵁ ⊤)) :
    (s • (show ToType (restrictGlobal V 𝒩) from z) : ToType (restrictGlobal V 𝒩)) =
      (show ToType (restrictGlobal V 𝒩) from
        (X.presheaf.map (eqToHom V.ι_image_top).op s) • z) := by
  refine Eq.trans (congrArg (fun r : ToType (V.toScheme.toRingedSpace.presheaf.obj (op ⊤)) =>
      (show ToType (restrictGlobal V 𝒩) from
        (r • (show Γ((Scheme.Modules.restrictFunctor V.ι).obj 𝒩, ⊤) from z))))
    (globalSectionsMap_app_top_alpha V s)) ?_
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply V.ι 𝒩 ⊤
    (X.presheaf.map (eqToHom V.ι_image_top).op s) z
  rw [Scheme.Opens.ι_appIso] at h
  exact h

/-- **Restriction of sections from `V` to `V.ι ''ᵁ ⊤`, as a map of `Γ(X, V)`-modules.**  Its
semilinearity is `Stacks.NaiveCotangentAffineMap.smul_restrictGlobal`. -/
def restrictTopLin : Γ(𝒩, V) →ₗ[Γ(X, V)] restrictGlobal V 𝒩 where
  toFun t := (𝒩.presheaf.map (eqToHom V.ι_image_top).op) t
  map_add' t t' := map_add _ t t'
  map_smul' s t :=
    Eq.trans (PresheafOfModules.map_smul 𝒩.val (eqToHom V.ι_image_top).op s t)
      (smul_restrictGlobal V 𝒩 s _).symm

/-- **The datum of Stacks 01BH, clause (4), for the sections of a sheaf of `𝒪_X`-modules over an
open.**  The sections of `𝒩` over `V` map, `Γ(X, V)`-linearly, to the global sections over `V` of
the restriction of `𝒩` along `V.ι`, by restriction along `V.ι ''ᵁ ⊤ = V`. -/
def restrictTop : ModuleCat.of Γ(X, V) Γ(𝒩, V) ⟶ restrictGlobal V 𝒩 :=
  ofHomTo (restrictGlobal V 𝒩) (restrictTopLin V 𝒩)

/-- `Stacks.NaiveCotangentAffineMap.restrictTop` is the restriction map of `𝒩`. -/
theorem restrictTop_apply (t : Γ(𝒩, V)) :
    restrictTop V 𝒩 t = (𝒩.presheaf.map (eqToHom V.ι_image_top).op) t := rfl

/-- **Restriction to the top open is natural.**  It commutes with a morphism of sheaves of
`𝒪_X`-modules, being a restriction map. -/
theorem restrictTop_naturality {𝒩' : X.Modules} (ε : 𝒩 ⟶ 𝒩') (t : Γ(𝒩, V)) :
    ((globalSectionsFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
        ((Scheme.Modules.restrictFunctor V.ι).map ε)) (restrictTop V 𝒩 t) =
      restrictTop V 𝒩' ((ε.val.app (op V)) t) :=
  PresheafOfModules.naturality_apply ε.val (eqToHom V.ι_image_top).op t

end Restrict

/-! ### Maps out of a two-term complex of associated sheaves -/

section Desc

variable (W : RingedSpace.{u, u}) {A : Type u} [CommRing A] (α : A →+* W.presheaf.obj (op ⊤))
  {M₁ M₀ : ModuleCat.{u} A} (δ : M₁ ⟶ M₀)
  (K : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing W)) ℤ)
  (g₁ : M₁ ⟶ (globalSectionsFunctor.{u, u} W α).obj (K.X (-1)))
  (g₀ : M₀ ⟶ (globalSectionsFunctor.{u, u} W α).obj (K.X 0))

/-- **A map out of a two-term complex of associated sheaves.**  Let `K` be a complex of sheaves of
`𝒪_W`-modules vanishing in degree `1`, and let `g₁` and `g₀` be `A`-linear maps of `M₁` and `M₀`
into the global sections of its terms in degrees `-1` and `0`, commuting with its differential.
Then the complex with `ℱ_{M₁}` in degree `-1` and `ℱ_{M₀}` in degree `0` maps to `K`, degreewise
by the adjoint of Stacks 01BH, clause (4).

Both halves of the commutation are read off from the adjunction: the two composites are the
images under `Stacks.AssociatedSheaf.associatedSheafAdjunction`'s hom-equivalence of the two
sides of the hypothesis. -/
def descDouble (hcomm : g₁ ≫ (globalSectionsFunctor.{u, u} W α).map (K.d (-1) 0) = δ ≫ g₀)
    (hz : Limits.IsZero (K.X 1)) :
    HomologicalComplex.double ((associatedSheafFunctor.{u, u} W α).map δ)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) ⟶ K :=
  HomologicalComplex.mkHomFromDouble _ (by decide)
    (associatedSheafDesc W α M₁ (K.X (-1)) g₁) (associatedSheafDesc W α M₀ (K.X 0) g₀)
    (by
      refine Eq.trans (Adjunction.homEquiv_naturality_right_symm
        (associatedSheafAdjunction.{u, u} W α) g₁ (K.d (-1) 0)).symm ?_
      refine Eq.trans (congrArg ((associatedSheafAdjunction.{u, u} W α).homEquiv M₁
        (K.X 0)).symm hcomm) ?_
      exact Adjunction.homEquiv_naturality_left_symm (associatedSheafAdjunction.{u, u} W α) δ g₀)
    (by
      intro k hk
      obtain rfl : k = 1 := by simpa using hk.symm
      exact hz.eq_of_tgt _ _)

/-- The degree `-1` component of `Stacks.NaiveCotangentAffineMap.descDouble` is the adjoint of
`g₁`. -/
theorem descDouble_f_negOne
    (hcomm : g₁ ≫ (globalSectionsFunctor.{u, u} W α).map (K.d (-1) 0) = δ ≫ g₀)
    (hz : Limits.IsZero (K.X 1)) :
    (descDouble W α δ K g₁ g₀ hcomm hz).f (-1) =
      (HomologicalComplex.doubleXIso₀ ((associatedSheafFunctor.{u, u} W α).map δ)
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom ≫
        associatedSheafDesc W α M₁ (K.X (-1)) g₁ :=
  HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _

/-- The degree `0` component of `Stacks.NaiveCotangentAffineMap.descDouble` is the adjoint of
`g₀`. -/
theorem descDouble_f_zero
    (hcomm : g₁ ≫ (globalSectionsFunctor.{u, u} W α).map (K.d (-1) 0) = δ ≫ g₀)
    (hz : Limits.IsZero (K.X 1)) :
    (descDouble W α δ K g₁ g₀ hcomm hz).f 0 =
      (HomologicalComplex.doubleXIso₁ ((associatedSheafFunctor.{u, u} W α).map δ)
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom ≫
        associatedSheafDesc W α M₀ (K.X 0) g₀ :=
  HomologicalComplex.mkHomFromDouble_f₁ _ _ _ _ _ _

end Desc

/-! ### The whole step: from a comparison on sections to a map of complexes -/

section WholeStep

variable {X : Scheme.{u}} (V : X.Opens)

/-- **The two data, restricted to the top open, still commute with the differentials.**  This is
`Stacks.NaiveCotangentAffineMap.restrictTop_naturality` applied to the differential of `N`. -/
theorem wholeStepMap_comm (N : CochainComplex X.Modules ℤ)
    {M₁ M₀ : ModuleCat.{u} Γ(X, V)} (δ : M₁ ⟶ M₀)
    (g₁ : M₁ ⟶ ModuleCat.of Γ(X, V) Γ(N.X (-1), V))
    (g₀ : M₀ ⟶ ModuleCat.of Γ(X, V) Γ(N.X 0, V))
    (hc : ∀ m : M₁, ((N.d (-1) 0).val.app (op V)) (g₁ m) = g₀ (δ m)) :
    (g₁ ≫ restrictTop V (N.X (-1))) ≫
        (globalSectionsFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
          ((((Scheme.Modules.restrictFunctor V.ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N).d (-1) 0) =
      δ ≫ (g₀ ≫ restrictTop V (N.X 0)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  change ((globalSectionsFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map
      ((Scheme.Modules.restrictFunctor V.ι).map (N.d (-1) 0)))
      (restrictTop V (N.X (-1)) (g₁ m)) = restrictTop V (N.X 0) (g₀ (δ m))
  exact Eq.trans (restrictTop_naturality V (N.X (-1)) (N.d (-1) 0) (g₁ m))
    (congrArg (restrictTop V (N.X 0)) (hc m))

/-- **Restriction along an open immersion preserves a vanishing term.**  The restriction functor
is additive, so it carries a zero object to a zero object. -/
theorem wholeStepMap_isZero (N : CochainComplex X.Modules ℤ) (hz : Limits.IsZero (N.X 1)) :
    Limits.IsZero ((((Scheme.Modules.restrictFunctor V.ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N).X 1) := by
  refine (Limits.IsZero.iff_id_eq_zero _).mpr ?_
  refine Eq.trans
    (CategoryTheory.Functor.map_id (Scheme.Modules.restrictFunctor V.ι) (N.X 1)).symm ?_
  refine Eq.trans (congrArg (Scheme.Modules.restrictFunctor V.ι).map
    ((Limits.IsZero.iff_id_eq_zero (N.X 1)).mp hz)) ?_
  exact CategoryTheory.Functor.map_zero _ _ _

/-- **The whole step of Stacks 0D0I's construction, over an abstract complex.**  Let `N` be a
complex of sheaves of `𝒪_X`-modules vanishing in degree `1`, let `δ : M₁ ⟶ M₀` be a map of
`Γ(X, V)`-modules and let `g₁` and `g₀` be maps of `Γ(X, V)`-modules into the sections over `V`
of the two terms of `N`, commuting with the differential of `N`.  Then the complex of sheaves of
`𝒪_V`-modules associated to `δ` maps to the restriction of `N` to `V`.

This is `Stacks.NaiveCotangentAffineMap.descDouble` applied to the restriction of `N` along
`V.ι`, the datum it consumes being produced from `g₁` and `g₀` by
`Stacks.NaiveCotangentAffineMap.restrictTop`.  Everything concrete about Stacks 0D0I enters only
through the arguments: this statement is what makes the construction affordable, since the
sheaves of modules occurring in `NL_{X/Y}` are sheafifications at which the elaborator cannot
afford to unfold anything. -/
def wholeStepMap (N : CochainComplex X.Modules ℤ)
    {M₁ M₀ : ModuleCat.{u} Γ(X, V)} (δ : M₁ ⟶ M₀)
    (g₁ : M₁ ⟶ ModuleCat.of Γ(X, V) Γ(N.X (-1), V))
    (g₀ : M₀ ⟶ ModuleCat.of Γ(X, V) Γ(N.X 0, V))
    (hc : ∀ m : M₁, ((N.d (-1) 0).val.app (op V)) (g₁ m) = g₀ (δ m))
    (hz : Limits.IsZero (N.X 1)) :
    HomologicalComplex.double
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map δ)
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) ⟶
      ((Scheme.Modules.restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj N :=
  descDouble V.toScheme.toRingedSpace (alpha (V := V)) δ _
    (g₁ ≫ restrictTop V (N.X (-1))) (g₀ ≫ restrictTop V (N.X 0))
    (wholeStepMap_comm V N δ g₁ g₀ hc) (wholeStepMap_isZero V N hz)

/-- **The degree `-1` component of `Stacks.NaiveCotangentAffineMap.wholeStepMap`** is the adjoint
of `g₁` followed by restriction to the top open.

The proof is written as an explicit `Eq.trans` through the unfolding of
`Stacks.NaiveCotangentAffineMap.wholeStepMap`, with every argument of
`Stacks.NaiveCotangentAffineMap.descDouble_f_negOne` supplied: left to unify the two sides on
its own the elaborator spends more than 200000 heartbeats on `isDefEq`, while the two steps
separately cost about 15000 and 8000. -/
theorem wholeStepMap_f_negOne (N : CochainComplex X.Modules ℤ)
    {M₁ M₀ : ModuleCat.{u} Γ(X, V)} (δ : M₁ ⟶ M₀)
    (g₁ : M₁ ⟶ ModuleCat.of Γ(X, V) Γ(N.X (-1), V))
    (g₀ : M₀ ⟶ ModuleCat.of Γ(X, V) Γ(N.X 0, V))
    (hc : ∀ m : M₁, ((N.d (-1) 0).val.app (op V)) (g₁ m) = g₀ (δ m))
    (hz : Limits.IsZero (N.X 1)) :
    (wholeStepMap V N δ g₁ g₀ hc hz).f (-1) =
      (HomologicalComplex.doubleXIso₀
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map δ)
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom ≫
        associatedSheafDesc V.toScheme.toRingedSpace (alpha (V := V)) M₁
          ((Scheme.Modules.restrictFunctor V.ι).obj (N.X (-1)))
          (g₁ ≫ restrictTop V (N.X (-1))) :=
  Eq.trans
    (show (wholeStepMap V N δ g₁ g₀ hc hz).f (-1) =
      (descDouble V.toScheme.toRingedSpace (alpha (V := V)) δ
        (((Scheme.Modules.restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (g₁ ≫ restrictTop V (N.X (-1))) (g₀ ≫ restrictTop V (N.X 0))
        (wholeStepMap_comm V N δ g₁ g₀ hc) (wholeStepMap_isZero V N hz)).f (-1) from rfl)
    (descDouble_f_negOne _ _ _ _ _ _ _ _)

/-- **The degree `0` component of `Stacks.NaiveCotangentAffineMap.wholeStepMap`** is the adjoint
of `g₀` followed by restriction to the top open. -/
theorem wholeStepMap_f_zero (N : CochainComplex X.Modules ℤ)
    {M₁ M₀ : ModuleCat.{u} Γ(X, V)} (δ : M₁ ⟶ M₀)
    (g₁ : M₁ ⟶ ModuleCat.of Γ(X, V) Γ(N.X (-1), V))
    (g₀ : M₀ ⟶ ModuleCat.of Γ(X, V) Γ(N.X 0, V))
    (hc : ∀ m : M₁, ((N.d (-1) 0).val.app (op V)) (g₁ m) = g₀ (δ m))
    (hz : Limits.IsZero (N.X 1)) :
    (wholeStepMap V N δ g₁ g₀ hc hz).f 0 =
      (HomologicalComplex.doubleXIso₁
        ((associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace (alpha (V := V))).map δ)
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom ≫
        associatedSheafDesc V.toScheme.toRingedSpace (alpha (V := V)) M₀
          ((Scheme.Modules.restrictFunctor V.ι).obj (N.X 0))
          (g₀ ≫ restrictTop V (N.X 0)) :=
  Eq.trans
    (show (wholeStepMap V N δ g₁ g₀ hc hz).f 0 =
      (descDouble V.toScheme.toRingedSpace (alpha (V := V)) δ
        (((Scheme.Modules.restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        (g₁ ≫ restrictTop V (N.X (-1))) (g₀ ≫ restrictTop V (N.X 0))
        (wholeStepMap_comm V N δ g₁ g₀ hc) (wholeStepMap_isZero V N hz)).f 0 from rfl)
    (descDouble_f_zero _ _ _ _ _ _ _ _)

end WholeStep

/-! ### The sections of the two terms of the naive cotangent complex -/

section Legs

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u}) (a : A ⟶ B) (W : Cᵒᵖ)

/-- **The degree `-1` term of `Stacks.SheafOfModules.naiveCotangentSections` is the sections of
the degree `-1` term of `NL_{B/A}`.**  Both are the sections over `W` of the conormal sheaf of the
canonical presentation; the identification is the one of
`Stacks.SheafOfModules.naiveCotangentComplex_X_negOne`, read on sections. -/
def sectionsLegNegOne :
    ModuleCat.of (ToType (B.obj.obj W)) ((naiveCotangentSections.{u, u, u, u} J A B a W).X₁) ⟶
      ModuleCat.of (ToType (B.obj.obj W))
        (ToType (((naiveCotangentComplex.{u, u, u, u} J A B a).X (-1)).val.obj W)) :=
  (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u} J A B a).symm).val.app W

/-- The degree `0` counterpart of
`Stacks.NaiveCotangentAffineMap.sectionsLegNegOne`. -/
def sectionsLegZero :
    ModuleCat.of (ToType (B.obj.obj W)) ((naiveCotangentSections.{u, u, u, u} J A B a W).X₀) ⟶
      ModuleCat.of (ToType (B.obj.obj W))
        (ToType (((naiveCotangentComplex.{u, u, u, u} J A B a).X 0).val.obj W)) :=
  (eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u} J A B a).symm).val.app W

/-- **The two identifications carry one differential to the other.**  The differential of
`Stacks.SheafOfModules.naiveCotangentSections`, which is the sections of the left-hand map of the
canonical conormal sequence, becomes the sections over `W` of the differential of `NL_{B/A}`.

Both statements are about the same morphism of sheaves of modules: the differential of `NL_{B/A}`
is that map conjugated by the two identifications
(`Stacks.SheafOfModules.naiveCotangentComplex_d_negOne_zero`), and one of the two cancels against
the identification already applied. -/
theorem sectionsLeg_comm (t : (naiveCotangentSections.{u, u, u, u} J A B a W).X₁) :
    ((naiveCotangentComplex.{u, u, u, u} J A B a).d (-1) 0).val.app W
        (sectionsLegNegOne J A B a W t) =
      sectionsLegZero J A B a W ((naiveCotangentSections.{u, u, u, u} J A B a W).d t) := by
  have key : (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u} J A B a).symm ≫
        (naiveCotangentComplex.{u, u, u, u} J A B a).d (-1) 0) =
      (canonicalConormalSequence.{u, u, u, u} J A B a).f ≫
        eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u} J A B a).symm := by
    rw [naiveCotangentComplex_d_negOne_zero.{u, u, u, u} J A B a, ← Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact ConcreteCategory.congr_hom (congrArg
    (fun φ : (canonicalConormalSequence.{u, u, u, u} J A B a).X₁ ⟶
        (naiveCotangentComplex.{u, u, u, u} J A B a).X 0 => φ.val.app W) key) t

end Legs

/-! ### The canonical map -/

section Concrete

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)

/-- **`NL_{X/Y}` read as a complex of sheaves of `𝒪_X`-modules.**  This is
`AlgebraicGeometry.Scheme.naiveCotangentComplex` with its target category spelled
`X.Modules`: the two are the same, but the module structure on the sections of a term is found by
instance search only in this spelling. -/
abbrev naiveCotangentModules : CochainComplex X.Modules ℤ := Scheme.naiveCotangentComplex f

/-- `Stacks.NaiveCotangentAffineMap.sectionsLegNegOne` at the canonical presentation of `𝒪_X`
over `f^{-1}𝒪_Y` and the open `V`. -/
def legNegOne :
    ModuleCat.of (ToType (X.sheaf.obj.obj (op V)))
        ((Stacks.NaiveCotangentAffineSections.naiveCotangentSections f V).X₁) ⟶
      ModuleCat.of Γ(X, V) Γ((naiveCotangentModules f).X (-1), V) :=
  sectionsLegNegOne (Opens.grothendieckTopology X.toRingedSpace.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) (op V)

/-- `Stacks.NaiveCotangentAffineMap.sectionsLegZero` at the canonical presentation of `𝒪_X` over
`f^{-1}𝒪_Y` and the open `V`. -/
def legZero :
    ModuleCat.of (ToType (X.sheaf.obj.obj (op V)))
        ((Stacks.NaiveCotangentAffineSections.naiveCotangentSections f V).X₀) ⟶
      ModuleCat.of Γ(X, V) Γ((naiveCotangentModules f).X 0, V) :=
  sectionsLegZero (Opens.grothendieckTopology X.toRingedSpace.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) (op V)

/-- The degree `-1` component of
`Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison`, as a morphism of
`Γ(X, V)`-modules. -/
def sectionsBaseHomNegOne :
    letI := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
    letI := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
    letI := Stacks.NaiveCotangentAffineSections.algebraSections f V
    haveI := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
    ModuleCat.of (ToType (X.sheaf.obj.obj (op V)))
        ((NaiveCotangent.NL (Algebra.Generators.self Γ(Y, U)
          (ToType (X.sheaf.obj.obj (op V))))).X₁) ⟶
      ModuleCat.of (ToType (X.sheaf.obj.obj (op V)))
        ((Stacks.NaiveCotangentAffineSections.naiveCotangentSections f V).X₁) := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  exact ModuleCat.ofHom (Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison f hVU).f₁

/-- The degree `0` component of
`Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison`, as a morphism of
`Γ(X, V)`-modules. -/
def sectionsBaseHomZero :
    letI := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
    letI := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
    letI := Stacks.NaiveCotangentAffineSections.algebraSections f V
    haveI := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
    ModuleCat.of (ToType (X.sheaf.obj.obj (op V)))
        ((NaiveCotangent.NL (Algebra.Generators.self Γ(Y, U)
          (ToType (X.sheaf.obj.obj (op V))))).X₀) ⟶
      ModuleCat.of (ToType (X.sheaf.obj.obj (op V)))
        ((Stacks.NaiveCotangentAffineSections.naiveCotangentSections f V).X₀) := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  exact ModuleCat.ofHom (Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison f hVU).f₀

/-- **The degree `-1` datum of Stacks 01BH, clause (4), for Stacks 0D0I.**  The conormal module
of the canonical presentation of `Γ(X, V)` over `Γ(Y, U)` maps, `Γ(X, V)`-linearly, to the
sections over `V` of the degree `-1` term of `NL_{X/Y}`. -/
def descDatumNegOne :
    nlSelfModNegOne f hVU ⟶ ModuleCat.of Γ(X, V) Γ((naiveCotangentModules f).X (-1), V) :=
  sectionsBaseHomNegOne f hVU ≫ legNegOne f

/-- **The degree `0` datum of Stacks 01BH, clause (4), for Stacks 0D0I.**  The cotangent space of
the canonical presentation of `Γ(X, V)` over `Γ(Y, U)` maps, `Γ(X, V)`-linearly, to the sections
over `V` of the degree `0` term of `NL_{X/Y}`. -/
def descDatumZero :
    nlSelfModZero f hVU ⟶ ModuleCat.of Γ(X, V) Γ((naiveCotangentModules f).X 0, V) :=
  sectionsBaseHomZero f hVU ≫ legZero f

/-- **The two data commute with the differentials.**  This is the `comm` field of
`Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison` read through
`Stacks.NaiveCotangentAffineMap.sectionsLeg_comm`. -/
theorem descDatum_comm (m : nlSelfModNegOne f hVU) :
    (((naiveCotangentModules f).d (-1) 0).val.app (op V)) (descDatumNegOne f hVU m) =
      descDatumZero f hVU (nlSelfModD f hVU m) := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  refine Eq.trans (sectionsLeg_comm (Opens.grothendieckTopology X.toRingedSpace.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) (op V)
    ((Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison f hVU).f₁ m)) ?_
  exact ConcreteCategory.congr_arg (legZero (V := V) f)
    (DFunLike.congr_fun (Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison f hVU).comm m)

/-- **The canonical map of Stacks 0D0I.**  For `f : X ⟶ Y` a morphism of schemes, `U` an open of
`Y` and `V` an open of `X` with `V ⊆ f^{-1}U`, writing `R = Γ(Y, U)` and `A = Γ(X, V)`, the
canonical map of complexes of sheaves of `𝒪_V`-modules

`(NL_{A/R})~ ⟶ NL_{X/Y}|_V`.

It is the map adjoint, degreewise, to the comparison on sections
`Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison` under the mapping property of the
sheaf associated to a module; no affineness of `U` or `V` is used in the construction, which
enters only in the assertion that this map is an isomorphism in `D(𝒪_V)`.

That assertion is not proved, so this declaration does not carry the tag 0D0I. -/
def comparisonMap :
    associatedNaiveCotangentComplex f hVU ⟶ restrictedNaiveCotangentComplex f (V := V) :=
  wholeStepMap V (naiveCotangentModules f) (nlSelfModD f hVU) (descDatumNegOne f hVU)
    (descDatumZero f hVU) (descDatum_comm f hVU)
    (Scheme.naiveCotangentComplex_isZero_X f 1 (by decide) (by decide))

end Concrete

end Stacks.NaiveCotangentAffineMap

end

end

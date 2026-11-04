module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesDiagonalCorrected
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDiagonalReduction
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualProved

/-!
# `Isom(E, E')` is an algebraic space of finite presentation, granted quasi-compact loci

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces
(`AlgebraicGeometry.Space.ComplexesSituation`), and let `x = (T, E)`, `y = (T, E')` be two objects
of `Complexes_{X/Y}` over the same test scheme `T`.  The corrected form of Stacks 0DPW
(`AlgebraicGeometry.Space.ComplexesSituation.complexesIsom_corrected_of_opens`) shows that the
relative derived Isom functor `Isom(E, E')` on the test schemes over `T` is an algebraic space of
finite presentation over `T`, from the conclusions of Stacks 0DLC for the four pairs
`(E, E')`, `(E', E)`, `(E, E)`, `(E', E')` and the quasi-compactness of the two opens
`W(E, E')`, `W(E', E)` of Stacks 0DLC, part (1).

Stacks 0DLC is proved in the library (`AlgebraicGeometry.Space.existsNegativeExtLocus_proved`,
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOverLocus_proved`,
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_proved`).  The quasi-compactness
of the loci is the gap in the source's proof of 0DPW; it is carried here as the hypothesis
`AlgebraicGeometry.Space.ComplexesSituation.NegativeExtLociQuasiCompact`.  Everything else is
discharged:

* the inclusion of an open subspace is an open immersion (the definition of an open subspace);
* a test scheme with vanishing negative fibre extensions factors through the locus of part (1)
  (`AlgebraicGeometry.Space.IsNegativeExtLocus.exists_lift_of_hasNoNegativeFibreExtOver`), by the
  characterisation of the locus at the points with values in a field and the fact that an open
  subspace is determined by those points;
* the two models `AlgebraicGeometry.Space.relativeDerivedHom` and
  `AlgebraicGeometry.Space.relativeDerivedHomFunctor` of the functor `T ↦ Hom(K_T, E_T)` agree
  (`AlgebraicGeometry.Space.relativeDerivedHomIsoFunctor`).

Nothing here is registered.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.NegativeExtLociQuasiCompact`: the opens of
  Stacks 0DLC, part (1), between two objects over one test scheme are quasi-compact.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.complexesIsom_corrected`: the corrected Stacks 0DPW
  at two objects over one test scheme, granted the quasi-compactness of the loci.
* `ComplexesSituation.isFinitePresentationAlgebraicSpaceOver_complexesIsom`: in particular
  `Isom(E, E')` is an algebraic space of finite presentation over `T`.

## References

* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- **The two models of the relative derived Hom functor on the test schemes agree.**  The
functor `AlgebraicGeometry.Space.relativeDerivedHom`, the restriction to the test schemes of the
relative Hom functor along the base changes over the algebraic spaces over `Y`, is the functor
`AlgebraicGeometry.Space.relativeDerivedHomFunctor` of the base changes along the test schemes:
both send `T` to `Hom(K_T, E_T)` with `X_T = X ×_Y T`, and the two cones of projections
`X_T ⟶ X` are the same up to the associativity of composition of functors
(`CategoryTheory.PullbackData.relHomFunctorConeIso`). -/
def relativeDerivedHomIsoFunctor (f : X ⟶ Y) (K E : derivedModules B S hS X) :
    relativeDerivedHom f K E ≅ relativeDerivedHomFunctor f K E :=
  (smallEtaleDerivedPullbackData B S hS).relHomFunctorConeIso
    (smallEtaleDerivedPullbackData_isCoherent B S hS)
    (PullbackData.ConeTo.ofOver (baseChangeOver f)) (overBaseChangeCone f) (schemesOverToOver Y)
    (Functor.associator _ _ _) (fun _ => Category.id_comp _) K E

/-- **A test scheme with vanishing negative fibre extensions factors through the locus of
Stacks 0DLC, part (1).**  If `W` is a locus of part (1) for `K` and `E` and the negative
extensions from `K` to `E` vanish on the fibres over every point of the test scheme `T` with
values in a field, then `T ⟶ Y` factors through `W`: an open subspace contains a section as soon
as it contains its restrictions to the spectra of fields
(`AlgebraicGeometry.Space.IsOpenSubspace.mem_of_forall_isFieldObject`), and such a restriction is
a point of `Y` at which the negative extensions vanish, hence lies in `|W|`. -/
theorem IsNegativeExtLocus.exists_lift_of_hasNoNegativeFibreExtOver {f : X ⟶ Y}
    {K E : derivedModules B S hS X} {W : OpenSubspaces B S hS Y.1}
    (hW : IsNegativeExtLocus f K E W) (T : SchemesOver Y) (hT : HasNoNegativeFibreExtOver f K E T) :
    ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ openSubspaceAsSpace B S hS W,
      t ≫ openSubspaceImmersion B S hS W = T.hom := by
  have hmem : testPoint T ∈ W.1.obj (op T.left) := by
    refine W.2.mem_of_forall_isFieldObject (testPoint T) (fun T₀ hT₀ t => ?_)
    let T₁ : SchemesOver Y := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom)
    let k : T₁ ⟶ T := CostructuredArrow.homMk t rfl
    have e : Y.1.map t.op (testPoint T) = testPoint T₁ := testPoint_naturality k
    rw [e]
    exact (hW T₁ hT₀).2 (hT T₁ hT₀ k)
  refine ⟨ObjectProperty.homMk (yonedaEquiv.symm ⟨testPoint T, hmem⟩), ?_⟩
  apply ObjectProperty.hom_ext
  apply yonedaEquiv.injective
  show yonedaEquiv (yonedaEquiv.symm
    (⟨testPoint T, hmem⟩ : W.1.toFunctor.obj (op T.left)) ≫ W.1.ι) = testPoint T
  rw [yonedaEquiv_comp]
  exact congrArg (fun x => W.1.ι.app (op T.left) x) (yonedaEquiv.apply_symm_apply _)

namespace ComplexesSituation

attribute [local instance] complexesCategory

variable (D : ComplexesSituation B S hS)

/-- **The opens of Stacks 0DLC, part (1), between two objects over one test scheme are
quasi-compact.**  For every test scheme `T` over `Y` and two objects `E`, `E'` of `D(𝒪_{X_T})`
satisfying conditions (1) and (2) of Stacks 0DLD, every open `W` of `T` characterised as in
Stacks 0DLC, part (1), for `Ext^{<0}(E, E')` is quasi-compact over `T`.

This is the input of the proof of Stacks 0DPW that the source leaves out: it applies Stacks 0DLC
as if the open `W(E, E')` were all of `T`. -/
def NegativeExtLociQuasiCompact : Prop :=
  ∀ (T : SchemesOver D.Y) (E E' : derivedModules B S hS (D.space T)),
    D.IsRelativelyPerfect T E → D.HasNoNegativeFibreExt T E →
    D.IsRelativelyPerfect T E' → D.HasNoNegativeFibreExt T E' →
    ∀ W : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj T.left).1,
      IsNegativeExtLocus (D.projection T) E E' W →
      IsQuasiCompact B S hS (openSubspaceImmersion B S hS W).hom

variable {D}

/-- **Stacks 0DLC, part (3), in the case `W = T`, for an object of `Complexes_{X/Y}`.**  For a
complex `K` on `X_T` satisfying conditions (1) and (2) of Stacks 0DLD, the functor
`T' ↦ Hom(K_{T'}, K_{T'})` on the test schemes over `T` is an algebraic space affine and of finite
presentation over `T`. -/
theorem isAffineFinitePresentation_relativeDerivedHomFunctor_self {T : SchemesOver D.Y}
    (K : derivedModules B S hS (D.space T)) (hK : D.IsRelativelyPerfect T K)
    (hX : D.HasNoNegativeFibreExt T K) :
    IsAffineFinitePresentationAlgebraicSpaceOver _
      (relativeDerivedHomFunctor (D.projection T) K K) :=
  (relativeDerivedHomRepresentableOfFibres_proved B S hS (D.projection T) (projection_isProper T)
    (D.projection_isFlat T) (projection_isFinitePresentation T) K K hK.1 hK
    (fun T₀ hT₀ => hasNoNegativeExtAt_self hX T₀ hT₀)).of_iso
    (relativeDerivedHomIsoFunctor (D.projection T) K K)

/-- **Stacks 0DLC, parts (1) and (3), between two objects over one test scheme.**  For complexes
`K`, `L` on `X_T` satisfying conditions (1) and (2) of Stacks 0DLD there is an open `W` of `T`
characterised as in Stacks 0DLC, part (1), for `Ext^{<0}(K, L)`; its inclusion `ι` is an open
immersion, every test scheme over `T` with vanishing negative fibre extensions from `K` to `L`
factors through it, and the functor `T' ↦ Hom(K_{T'}, L_{T'})` on the test schemes over `W` is an
algebraic space affine and of finite presentation over `W`. -/
theorem exists_negativeExtLocus_relativeDerivedHomFunctor {T : SchemesOver D.Y}
    (K L : derivedModules B S hS (D.space T)) (hK : D.IsRelativelyPerfect T K)
    (hL : D.IsRelativelyPerfect T L) :
    ∃ W : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj T.left).1,
      IsNegativeExtLocus (D.projection T) K L W ∧
      IsOpenImmersion B S hS (openSubspaceImmersion B S hS W).hom ∧
      (∀ T', HasNoNegativeFibreExtOver (D.projection T) K L T' →
        ∃ t : (schemeSpaceFunctor B S hS).obj T'.left ⟶ openSubspaceAsSpace B S hS W,
          t ≫ openSubspaceImmersion B S hS W = T'.hom) ∧
      IsAffineFinitePresentationAlgebraicSpaceOver (openSubspaceAsSpace B S hS W)
        ((CostructuredArrow.map (openSubspaceImmersion B S hS W)).op ⋙
          relativeDerivedHomFunctor (D.projection T) K L) := by
  obtain ⟨W, hW⟩ := existsNegativeExtLocus_proved B S hS (D.projection T) (projection_isProper T)
    (D.projection_isFlat T) (projection_isFinitePresentation T) K L hK.1 hL
  exact ⟨W, hW, W.2.2, hW.exists_lift_of_hasNoNegativeFibreExtOver,
    (relativeDerivedHomRepresentableOverLocus_proved B S hS (D.projection T)
      (projection_isProper T) (D.projection_isFlat T) (projection_isFinitePresentation T) K L hK.1
      hL W hW).of_iso
      (Functor.isoWhiskerLeft _ (relativeDerivedHomIsoFunctor (D.projection T) K L))⟩

/-- **The corrected Stacks 0DPW at two objects of `Complexes_{X/Y}` over one test scheme, granted
the quasi-compactness of the loci of Stacks 0DLC, part (1).**  For objects `x = (T, E)` and
`y = (T, E')`, the presheaf `Isom(x, y)` on `(Sch/T)` is the relative derived Isom functor; there
is a quasi-compact open `W ⊆ T` (the intersection `W(E, E') ∩ W(E', E)` of the loci of
Stacks 0DLC, part (1)) through which `Isom(E, E')` factors, over which it is affine and of finite
presentation, and `Isom(E, E')` is an algebraic space of finite presentation over `T`.

This is `AlgebraicGeometry.Space.ComplexesSituation.complexesIsom_corrected_of_opens` with the
conclusions of Stacks 0DLC discharged; the only remaining input is
`AlgebraicGeometry.Space.ComplexesSituation.NegativeExtLociQuasiCompact`. -/
theorem complexesIsom_corrected (hW : D.NegativeExtLociQuasiCompact)
    (A : ComplexesObject D) (E' : derivedModules B S hS (D.space A.T))
    (h₁ : D.IsRelativelyPerfect A.T E') (h₂ : D.HasNoNegativeFibreExt A.T E') :
    Nonempty ((complexesFunctor D).isomPresheaf ⟨A, rfl⟩ ⟨sameTest A E' h₁ h₂, rfl⟩ ≅
      (overSchemeTest A.T.left).op ⋙ relativeDerivedIsomFunctor (D.projection A.T) A.E E') ∧
    ∃ (W : AlgebraicSpaces B S hS) (ι : W ⟶ (schemeSpaceFunctor B S hS).obj A.T.left),
      IsOpenImmersion B S hS ι.hom ∧ IsQuasiCompact B S hS ι.hom ∧
      (∀ T', Nonempty ((relativeDerivedIsomFunctor (D.projection A.T) A.E E').obj (op T')) →
        ∃ t : (schemeSpaceFunctor B S hS).obj T'.left ⟶ W, t ≫ ι = T'.hom) ∧
      IsAffineFinitePresentationAlgebraicSpaceOver W
        ((CostructuredArrow.map ι).op ⋙ relativeDerivedIsomFunctor (D.projection A.T) A.E E') ∧
      IsFinitePresentationAlgebraicSpaceOver _
        (relativeDerivedIsomFunctor (D.projection A.T) A.E E') := by
  obtain ⟨W₁, hW₁, hι₁, hf₁, hEE'⟩ :=
    exists_negativeExtLocus_relativeDerivedHomFunctor A.E E' A.relativelyPerfect h₁
  obtain ⟨W₂, hW₂, hι₂, hf₂, hE'E⟩ :=
    exists_negativeExtLocus_relativeDerivedHomFunctor E' A.E h₁ A.relativelyPerfect
  obtain ⟨hiso, W, ι, hι, hqc, -, -, hfac, hW', hfp⟩ := complexesIsom_corrected_of_opens A E' h₁ h₂
    (openSubspaceImmersion B S hS W₁) (openSubspaceImmersion B S hS W₂) hι₁ hι₂
    (hW A.T A.E E' A.relativelyPerfect A.noNegativeFibreExt h₁ h₂ W₁ hW₁)
    (hW A.T E' A.E h₁ h₂ A.relativelyPerfect A.noNegativeFibreExt W₂ hW₂) hf₁ hf₂ hEE' hE'E
    (isAffineFinitePresentation_relativeDerivedHomFunctor_self A.E A.relativelyPerfect
      A.noNegativeFibreExt)
    (isAffineFinitePresentation_relativeDerivedHomFunctor_self E' h₁ h₂)
  exact ⟨hiso, W, ι, hι, hqc, hfac, hW', hfp⟩

/-- **`Isom(E, E')` is an algebraic space of finite presentation over the test scheme**, granted
the quasi-compactness of the loci of Stacks 0DLC, part (1): for objects `(T, E)` and `(T, E')` of
`Complexes_{X/Y}` over the same test scheme, the relative derived Isom functor of `E` and `E'`
along `X_T ⟶ T` is an algebraic space of finite presentation over `T`. -/
theorem isFinitePresentationAlgebraicSpaceOver_complexesIsom (hW : D.NegativeExtLociQuasiCompact)
    (A : ComplexesObject D) (E' : derivedModules B S hS (D.space A.T))
    (h₁ : D.IsRelativelyPerfect A.T E') (h₂ : D.HasNoNegativeFibreExt A.T E') :
    IsFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj A.T.left)
      (relativeDerivedIsomFunctor (D.projection A.T) A.E E') := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := complexesIsom_corrected hW A E' h₁ h₂
  exact h

end ComplexesSituation

end AlgebraicGeometry.Space

end

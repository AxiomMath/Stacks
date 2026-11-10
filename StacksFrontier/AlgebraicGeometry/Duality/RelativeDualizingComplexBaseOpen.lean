module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex

/-!
# Diagonal opens over an open of the base

Let `g : X ⟶ T` be a morphism of schemes and `j : T ⟶ S` an open immersion. Since `j` is a
monomorphism, `X ×_S X = X ×_T X`, so an open `W ⊆ X ×_S X` through which the diagonal of
`g ≫ j` factors as a closed immersion `Δ : X ⟶ W` is the same thing as such an open for `g`.
The map `Δ_*𝒪_X ⟶ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)` that a morphism `ξ` defines (Stacks
0E2T) only sees `W`, `Δ` and the first projection `W ⟶ X`, which agree for the two readings. This
is the step "`U ×_V U = U ×_S U`" of the proof of Stacks 0E2X.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.pullbackCompMonoIso`: `X ×_S X ≅ X ×_T X`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.ofComp`: a diagonal open of `g ≫ j`, read as one
  of `g`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_isIso_diagonalAction_of_ofComp`: the
  diagonal condition of Stacks 0E2T passes from `D.ofComp` to `D`.

## Implementation notes

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, read with the
same instances as in `StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex`, where
`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalAction` is defined; the map is restated here
with the first projection as a variable, which needs the restatement to elaborate to the same
term.

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] HasDerivedCategory.standard

/-! ### Diagonal opens over an open of the base -/

variable {X T S : Scheme.{u}} (g : X ⟶ T) (j : T ⟶ S) [IsOpenImmersion j]

/-- `X ×_S X ≅ X ×_T X` for `T ⟶ S` an open immersion, a monomorphism. -/
def pullbackCompMonoIso : pullback (g ≫ j) (g ≫ j) ≅ pullback g g where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    ((cancel_mono j).1 (by
      rw [Category.assoc, Category.assoc]; exact pullback.condition (f := g ≫ j) (g := g ≫ j)))
  inv := pullback.lift (pullback.fst g g) (pullback.snd g g)
    (by rw [← Category.assoc, pullback.condition, Category.assoc])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

/-- The isomorphism `X ×_S X ≅ X ×_T X` commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem pullbackCompMonoIso_hom_fst :
    (pullbackCompMonoIso g j).hom ≫ pullback.fst g g = pullback.fst (g ≫ j) (g ≫ j) :=
  pullback.lift_fst _ _ _

/-- The isomorphism `X ×_S X ≅ X ×_T X` commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem pullbackCompMonoIso_hom_snd :
    (pullbackCompMonoIso g j).hom ≫ pullback.snd g g = pullback.snd (g ≫ j) (g ≫ j) :=
  pullback.lift_snd _ _ _

variable {g j}

/-- **A diagonal open of `g ≫ j` is a diagonal open of `g`**, for `j` an open immersion: the
same open `W` and the same closed immersion `Δ : X ⟶ W`, through `X ×_S X ≅ X ×_T X`. -/
abbrev ofComp (D : DiagonalOpen (g ≫ j)) : DiagonalOpen g where
  W := D.W
  ι := D.ι ≫ (pullbackCompMonoIso g j).hom
  isOpenImmersion := by have := D.isOpenImmersion; infer_instance
  diag := D.diag
  isClosedImmersion := D.isClosedImmersion
  fac := by
    rw [← Category.assoc, D.fac]
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackCompMonoIso_hom_fst, pullback.diagonal_fst,
        pullback.diagonal_fst]
    · rw [Category.assoc, pullbackCompMonoIso_hom_snd, pullback.diagonal_snd,
        pullback.diagonal_snd]

/-- The first projection `W ⟶ X` of `D.ofComp` is that of `D`. -/
theorem ofComp_proj (D : DiagonalOpen (g ≫ j)) : (D.ofComp).proj = D.proj := by
  change (D.ι ≫ (pullbackCompMonoIso g j).hom) ≫ pullback.fst g g = D.ι ≫ pullback.fst _ _
  rw [Category.assoc, pullbackCompMonoIso_hom_fst]

/-! The universes of the site `Opens W` and of the sections of `𝒪_W` coincide, so the
additivity of the tensor product and the existence of the total tensor complexes are named
rather than synthesized, as in `StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex`.
-/

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- `L p^*K` for a morphism `p : W ⟶ X`, as an object of `D(𝒪_W)`. -/
abbrev derivedPullbackAlong {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f) (p : D.W ⟶ X)
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    DerivedCategory (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p.toLRSHom.toShHom).obj K

/-- The map that `ξ` defines depends on the diagonal open only through `W`, `Δ` and the first
projection: two first projections that agree give maps that are isomorphisms together. -/
theorem exists_isIso_of_proj_eq {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (p : D.W ⟶ X) (hp : p = D.proj)
    (ξ : D.diagonalObject ⟶ D.derivedPullbackAlong p K)
    (h : IsIso ((Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
      D.diagonalObject (D.derivedPullbackAlong p K)).symm
      (Stacks.RelativeSpec.AlgebraSheaf.derivedMul D.diagonalAlgebra ≫ ξ))) :
    ∃ ξ' : D.diagonalObject ⟶ D.derivedPullbackProj K, IsIso (D.diagonalAction K ξ') := by
  subst hp
  refine ⟨ξ, ?_⟩
  unfold diagonalAction
  convert h using 2

/-- **The diagonal condition over an open of the base.** The diagonal open `D.ofComp` of `g` has
the same `W`, the same `Δ` and the same first projection as the diagonal open `D` of `g ≫ j`, so
if some `ξ` defines an isomorphism for `D.ofComp`, some `ξ'` does for `D`. -/
theorem exists_isIso_diagonalAction_of_ofComp (D : DiagonalOpen (g ≫ j))
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.ofComp.diagonalObject ⟶ D.ofComp.derivedPullbackProj K)
    (h : IsIso (D.ofComp.diagonalAction K ξ)) :
    ∃ ξ' : D.diagonalObject ⟶ D.derivedPullbackProj K, IsIso (D.diagonalAction K ξ') := by
  obtain ⟨ξ', hξ'⟩ := D.exists_isIso_of_proj_eq K D.ofComp.proj (ofComp_proj D) ξ (by
    unfold diagonalAction at h
    convert h using 2)
  exact ⟨ξ', hξ'⟩

universe d₁ d₂

/-- **A relative dualizing complex over an open of the base is one over the base**, for the
diagonal condition: if `(K, ξ)` is a relative dualizing complex for `g` relative to `D.ofComp`,
and `K` is perfect relative to `S` along `g ≫ j`, then some `ξ'` makes `(K, ξ')` a relative
dualizing complex for `g ≫ j` relative to `D`. -/
theorem exists_isRelativeDualizingComplex_of_ofComp [Flat g] [LocallyOfFinitePresentation g]
    [Flat (g ≫ j)] [LocallyOfFinitePresentation (g ≫ j)]
    [HasDerivedCategory.{d₁} (OXMod.{u, u} (RingedSpace.inverseImage T.toRingedSpace g.base))]
    [∀ U : TopologicalSpace.Opens (RingedSpace.inverseImage T.toRingedSpace g.base).carrier,
      HasDerivedCategory.{d₁} (OXMod.{u, u}
        ((RingedSpace.inverseImage T.toRingedSpace g.base).restrict U.isOpenEmbedding))]
    [HasDerivedCategory.{d₂}
      (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base))]
    [∀ U : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base).carrier,
      HasDerivedCategory.{d₂} (OXMod.{u, u}
        ((RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base).restrict U.isOpenEmbedding))]
    (Dten₁ : ∀ U : TopologicalSpace.Opens (RingedSpace.inverseImage T.toRingedSpace g.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d₁, u}
        ((RingedSpace.inverseImage T.toRingedSpace g.base).restrict U.isOpenEmbedding))
    (Dten₂ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d₂, u}
        ((RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base).restrict U.isOpenEmbedding))
    (D : DiagonalOpen (g ≫ j)) (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.ofComp.diagonalObject ⟶ D.ofComp.derivedPullbackProj K)
    (h : IsRelativeDualizingComplex g Dten₁ D.ofComp K ξ)
    (hK : IsPerfectRelativeTo (g ≫ j) Dten₂ K) :
    ∃ ξ' : D.diagonalObject ⟶ D.derivedPullbackProj K,
      IsRelativeDualizingComplex (g ≫ j) Dten₂ D K ξ' := by
  obtain ⟨ξ', hξ'⟩ := D.exists_isIso_diagonalAction_of_ofComp K ξ h.isIso_diagonalAction
  exact ⟨ξ', ⟨hK, hξ'⟩⟩

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end

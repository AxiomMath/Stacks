module

public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentStalk
public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentRestrictionSheaf
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# Tag 08T3: the cotangent complex of a morphism of schemes on an affine open

Let `f : X ⟶ Y` be a morphism of schemes, `U = Spec B ⊂ X` and `V = Spec A ⊂ Y` affine opens with
`f(U) ⊂ V`. Tag 08T3 asserts that there is a canonical map of complexes

`~(L_{B/A}) ⟶ L_{X/Y}|_U`

which is an isomorphism in `D(𝒪_U)`, and that this map is compatible with restricting to
smaller affine opens. The canonical map is `AlgebraicGeometry.Scheme.Hom.affineCotangentComparison`
of `StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentComparison`, and its compatibility with
restriction is `AlgebraicGeometry.Scheme.Hom.affineCotangentComparison_restriction` of
`StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentRestrictionSheaf`. This file proves that
it is
an isomorphism in `D(𝒪_U)`, and registers the three assertions together.

## The proof

The proof is the one of the source: quasi-isomorphy is checked on stalks (Tag 08TL,
`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso`). At a point `y` of
`Spec B`, with image `x ∈ U`:

* the stalk of `~(L_{B/A})` is `𝒪_{Spec B, y} ⊗_B L_{B/A}` (Schemes, Lemma 01HV,
  `Stacks.TildeStalk.tildeStalkFunctorIso`);
* the stalk of `L_{X/Y}|_U` is the cotangent complex of `(f⁻¹𝒪_Y)_x → 𝒪_{Spec B, y}`
  (`AlgebraicGeometry.Scheme.Hom.restrictedStalkIso`: Tag 08SX and Tag 08S9 at the stalk);
* under these identifications the stalk of the canonical map is the adjoint functoriality map
  `𝒪_{Spec B, y} ⊗_B L_{B/A} ⟶ L_{𝒪_{Spec B, y}/(f⁻¹𝒪_Y)_x}`. Both maps are `B`-semilinear and
  agree on the elements `1 ⊗ m`, and `𝒪_{Spec B, y} ⊗_B L_{B/A}` is a localization of `L_{B/A}`,
  so they agree (`ModuleCat.extendScalars_addMonoidHom_ext_of_isLocalization`);
* that map is a quasi-isomorphism because `𝒪_{Spec B, y} = B_𝔭` and `(f⁻¹𝒪_Y)_x = A_𝔮` are
  localizations (Tags 08SF and 08R2,
  `CommAlgCat.quasiIso_squareCotangentExtendScalarsMap_of_isLocalization`); this is where the
  affineness of `V` is used.

## Main results

* `AlgebraicGeometry.Scheme.Hom.quasiIso_affineCotangentComparison`: the canonical map is a
  quasi-isomorphism.
* `AlgebraicGeometry.Scheme.Hom.affineCotangentComparison_spec`: **Tag 08T3**, all three
  assertions.

## References

* [Stacks Project, Tag 08T3](https://stacks.math.columbia.edu/tag/08T3)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08SF](https://stacks.math.columbia.edu/tag/08SF)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open scoped ChangeOfRings

universe w u

namespace ModuleCat

/-- **Additive maps out of a base change to a localization are determined on `1 ⊗ m`.** Let
`φ : R → S` be a localization. Two additive maps out of `S ⊗_R M` into an `S`-module, both
commuting with the action of `R` through `φ`, agree as soon as they agree on the elements
`1 ⊗ m`. -/
theorem extendScalars_addMonoidHom_ext_of_isLocalization {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) (T : Submonoid R) (hφ : @IsLocalization R _ T S _ φ.toAlgebra)
    {M : ModuleCat.{u} R} {Q : Type u} [AddCommGroup Q] [Module S Q]
    (θ₁ θ₂ : (extendScalars φ).obj M →+ Q)
    (h₁ : ∀ (r : R) (w : (extendScalars φ).obj M), θ₁ (φ r • w) = φ r • θ₁ w)
    (h₂ : ∀ (r : R) (w : (extendScalars φ).obj M), θ₂ (φ r • w) = φ r • θ₂ w)
    (h : ∀ m : M, θ₁ ((1 : S) ⊗ₜ[R, φ] m) = θ₂ ((1 : S) ⊗ₜ[R, φ] m)) : θ₁ = θ₂ := by
  let := φ.toAlgebra
  have key : ∀ θ : (extendScalars φ).obj M →+ Q,
      (∀ (r : R) (w : (extendScalars φ).obj M), θ (φ r • w) = φ r • θ w) →
      ∀ (c : R) (t : T) (m : M), φ t • θ (IsLocalization.mk' S c t ⊗ₜ[R, φ] m) =
        φ c • θ ((1 : S) ⊗ₜ[R, φ] m) := by
    intro θ hθ c t m
    let tm : S → (extendScalars φ).obj M := fun s => s ⊗ₜ[R, φ] m
    have e₁ : φ t * IsLocalization.mk' S c t = φ c * 1 :=
      (IsLocalization.mk'_spec' S c t).trans (mul_one (φ c)).symm
    have e₂ : φ t • tm (IsLocalization.mk' S c t) = φ c • tm 1 :=
      (ExtendScalars.smul_tmul φ _ _ m).trans
        ((congrArg tm e₁).trans (ExtendScalars.smul_tmul φ _ _ m).symm)
    exact (hθ t _).symm.trans ((congrArg θ e₂).trans (hθ c _))
  refine AddMonoidHom.ext fun w => ?_
  refine TensorProduct.inductionOn (R := R) (M := (restrictScalars φ).obj (of S S)) (N := M)
    (motive := fun w => θ₁ w = θ₂ w) w ?_ ?_
  · intro s m
    obtain ⟨⟨c, t⟩, hs⟩ := IsLocalization.mk'_surjective T (show S from s)
    have hu : IsUnit (φ t) := IsLocalization.map_units S t
    rw [← hs]
    exact hu.smul_left_cancel.mp ((key θ₁ h₁ c t m).trans
      ((congrArg (fun z => φ c • z) (h m)).trans (key θ₂ h₂ c t m).symm))
  · intro a b ha hb
    exact ((map_add θ₁ a b).trans (congrArg₂ (· + ·) ha hb)).trans (map_add θ₂ a b).symm

end ModuleCat


namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Scheme.Modules.toPresheaf_additive
  Scheme.Modules.toPresheaf_stalkFunctor_additive

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)


/-- On global sections, the canonical map `~(L_{B/A}) ⟶ L_{X/Y}|_U` carries the global section of
`~(L_{B/A})` attached to `m ∈ L_{B/A}` to the image of `m` under the canonical map
`L_{B/A} ⟶ Γ(L_{X/Y}|_U)` of which it is the adjunct. -/
theorem affineCotangentComparison_app_toOpen (k : ℤ)
    (m : (CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)).X k) :
    ((affineCotangentComparison f hU e).f k).val.app (op ⊤)
        ((tilde.toOpen ((CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)).X k)
          ⊤) m) =
      (gammaCotangentComparison f hU e).f k m := by
  let N := (restrictedCotangentComplex f hU).X k
  have h₁ := ConcreteCategory.congr_hom (tilde.toOpen_map_app
    ((gammaCotangentComparison f hU e).f k) ⊤) m
  have h₂ := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app N ⊤)
    ((gammaCotangentComparison f hU e).f k m)
  have hid : (homOfLE le_top : (⊤ : (Spec Γ(X, U)).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [hid, op_id, CategoryTheory.Functor.map_id] at h₂
  exact (congrArg (fun z => (N.fromTildeΓ).val.app (op ⊤) z) h₁).trans h₂

include hV in
/-- The stalk at `y ∈ Spec 𝒪_X(U)` of the canonical map `~(L_{B/A}) ⟶ L_{X/Y}|_U` is a
quasi-isomorphism of complexes of modules over the stalk ring. -/
theorem quasiIso_stalk_affineCotangentComparison (y : PrimeSpectrum Γ(X, U)) :
    QuasiIso (((Stacks.TildeStalk.specStalkFunctor Γ(X, U) (specPoint y)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (affineCotangentComparison f hU e)) := by
  let F := Stacks.TildeStalk.specStalkFunctor Γ(X, U) (specPoint y)
  let Lba := CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)
  let ψ := CommAlgCat.squareCotangentExtendScalarsMap (specStalkSquare f hU e y)
  let := Stacks.RingedSpace.structureStalkCommRing (Spec Γ(X, U)).toRingedSpace y
  have hψ : QuasiIso ψ :=
    CommAlgCat.quasiIso_squareCotangentExtendScalarsMap_of_isLocalization
      (specStalkSquare f hU e y) _ y.asIdeal.primeCompl
      (isLocalization_stalkSquare_base f hU hV e y) (isLocalization_specStalkRingHom Γ(X, U) y)
  let fg := forget₂ (ModuleCat.{u} (specStalkAlgebra f hU e y : Type u)) AddCommGrpCat.{u}
  have hψ' : QuasiIso ((fg.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) := inferInstance
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ fg]
  let E := (NatIso.mapHomologicalComplex (Stacks.TildeStalk.tildeStalkFunctorIso Γ(X, U)
    (specPoint y)) (ComplexShape.up ℤ)).app Lba
  let left := (fg.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso E
  let right := restrictedStalkIso f hU e y
  have comm : left.hom ≫ (fg.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ =
      (fg.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (affineCotangentComparison f hU e)) ≫
        right.hom := by
    have key : ∀ k, left.inv.f k ≫ ((fg.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (affineCotangentComparison f hU e))).f k ≫ right.hom.f k =
        ((fg.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ).f k := by
      intro k
      let tI := (Stacks.TildeStalk.tildeStalkFunctorIso Γ(X, U) (specPoint y)).app (Lba.X k)
      let φk := (affineCotangentComparison f hU e).f k
      refine AddCommGrpCat.hom_ext (ModuleCat.extendScalars_addMonoidHom_ext_of_isLocalization
        (Stacks.TildeStalk.specStalkRingHom Γ(X, U) y) y.asIdeal.primeCompl
        (isLocalization_specStalkRingHom Γ(X, U) y) (M := Lba.X k)
        (Q := ((CommAlgCat.cotangentComplex.{u, u} _ (specStalkAlgebra f hU e y)).X k)) _ _
        ?_ ?_ ?_)
      · intro r w
        refine (congrArg (fun z => right.hom.f k ((F.map φk).hom z))
          (tI.inv.hom.map_smul _ w)).trans ?_
        refine (congrArg (fun z => right.hom.f k z) ((F.map φk).hom.map_smul _ _)).trans ?_
        exact restrictedStalkIso_hom_smul f hU e y k r _
      · intro r w
        exact (ψ.f k).hom.map_smul _ w
      · intro m
        have hgerm := Stacks.TildeStalk.tildeStalkFunctorIso_hom_app_germ_toOpen Γ(X, U)
          (specPoint y) (Lba.X k) m
        have hE : tI.inv.hom ((1 : (specStalkAlgebra f hU e y : Type u)) ⊗ₜ[Γ(X, U),
            Stacks.TildeStalk.specStalkRingHom Γ(X, U) y] m) =
            (TopCat.Presheaf.germ ((tilde.functor Γ(X, U)).obj (Lba.X k)).val.presheaf ⊤
              (specPoint y) trivial).hom ((tilde.toOpen (Lba.X k) ⊤).hom m) :=
          (congrArg tI.inv.hom hgerm.symm).trans (Iso.hom_inv_id_apply tI _)
        have hF := TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) ⊤
          (specPoint y) trivial ((PresheafOfModules.toPresheaf _).map φk.val)
          ((tilde.toOpen (Lba.X k) ⊤).hom m)
        have hφ := affineCotangentComparison_app_toOpen f hU e k m
        have hR := restrictedStalkIso_hom_germ f hU e y k m
        have hψm : (ψ.f k).hom ((1 : (specStalkAlgebra f hU e y : Type u)) ⊗ₜ[Γ(X, U),
            Stacks.TildeStalk.specStalkRingHom Γ(X, U) y] m) =
            (CommAlgCat.squareCotangentComplexMap.{u, u, u} (specStalkSquare f hU e y)).f k m :=
          ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul _ _ _
        refine (congrArg (fun z => right.hom.f k ((F.map φk).hom z)) hE).trans ?_
        refine (congrArg (fun z => right.hom.f k z) hF).trans ?_
        refine (congrArg (fun z => right.hom.f k ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((restrictedCotangentComplex f hU).X k).presheaf ⊤ (specPoint y) trivial) z))
          hφ).trans ?_
        exact hR.trans hψm.symm
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    have hli : left.hom.f k ≫ left.inv.f k = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    refine (HomologicalComplex.comp_f _ _ k).trans ?_
    refine ((congrArg (fun t => left.hom.f k ≫ t) (key k)).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => t ≫ _) hli).trans ?_
    refine (Category.id_comp _).trans ?_
    exact (HomologicalComplex.comp_f _ _ k).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk left right comm)).2 hψ'

include hV in
/-- **The canonical map of Tag 08T3 is a quasi-isomorphism.** For a morphism of schemes
`f : X ⟶ Y` and affine opens `U = Spec B ⊂ X`, `V = Spec A ⊂ Y` with `f(U) ⊂ V`, the canonical
map `~(L_{B/A}) ⟶ L_{X/Y}|_U` is a quasi-isomorphism of complexes of `𝒪_U`-modules: it is so on
every stalk (Tag 08TL). -/
theorem quasiIso_affineCotangentComparison : QuasiIso (affineCotangentComparison f hU e) :=
  AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso
    (structureSheafRing (Spec Γ(X, U)).toRingedSpace) _
    fun y => quasiIso_stalk_affineCotangentComparison f hU hV e y

include hV in
/-- **The canonical map of Tag 08T3 is an isomorphism in `D(𝒪_U)`**, for any model of the
derived category. -/
theorem isIso_Q_map_affineCotangentComparison
    [HasDerivedCategory.{w} (Spec Γ(X, U)).Modules] :
    IsIso (DerivedCategory.Q.map (affineCotangentComparison f hU e)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_affineCotangentComparison f hU hV e)

include hV in
/-- **Stacks Project, Tag 08T3.**

Let `f : X ⟶ Y` be a morphism of schemes and let `U = Spec B ⊂ X` and `V = Spec A ⊂ Y` be
affine opens with `f(U) ⊂ V`, so that `B = 𝒪_X(U)` and `A = 𝒪_Y(V)`. The map of complexes
`AlgebraicGeometry.Scheme.Hom.affineCotangentComparison f hU e : ~(L_{B/A}) ⟶ L_{X/Y}|_U`
satisfies the three assertions of the lemma:

1. it is **the canonical map**: in every degree it is the adjunct, under the universal property
   of `~` (Tag 01I7), of the canonical map `L_{B/A} ⟶ Γ(L_{X/Y}|_U)`,
   `AlgebraicGeometry.Scheme.Hom.gammaCotangentComparison`, which is the map
   `L_{B/A} ⟶ L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}` induced by `A ⟶ (f⁻¹𝒪_Y)(U)` followed by the canonical map
   `L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)} ⟶ L_{X/Y}(U)` of Remark 08SX;
2. it is **an isomorphism in `D(𝒪_U)`**;
3. it is **compatible with restricting to smaller affine opens** `U' ⊂ U` of `X` and `V' ⊂ V` of
   `Y` with `f(U') ⊂ V'`: the square formed by the canonical maps for `(U, V)` and `(U', V')`
   and the two restriction maps commutes. -/
@[stacks 08T3 "the whole lemma, in one covering statement: (1) the canonical map, pinned as the \
adjunct under the tilde-Gamma adjunction of the canonical map L_{B/A} -> Gamma(L_{X/Y}|_U) built \
from A -> (f^{-1}O_Y)(U) and Remark 08SX; (2) it is an isomorphism in D(O_U); (3) it is \
compatible with restriction to smaller affine opens U' of X and opens V' of Y. Hypotheses: \
exactly the source's, U and V affine with f(U) inside V"]
theorem affineCotangentComparison_spec [HasDerivedCategory.{w} (Spec Γ(X, U)).Modules] :
    (∀ j : ℤ, (tilde.adjunction (R := Γ(X, U))).homEquiv _ _
        ((affineCotangentComparison f hU e).f j) = (gammaCotangentComparison f hU e).f j) ∧
    IsIso (DerivedCategory.Q.map (affineCotangentComparison f hU e)) ∧
    ∀ {U' : X.Opens} (hU' : IsAffineOpen U') {V' : Y.Opens} (e' : U' ≤ f ⁻¹ᵁ V')
      (hUle : U' ≤ U) (hVle : V' ≤ V),
      affineCotangentComparison f hU e ≫
          Stacks.AffineCotangentSheaf.restrictedCotangentRestriction f hU hU' hUle =
        Stacks.AffineCotangentSheaf.tildeCotangentRestriction f e e' hUle hVle ≫
          ((Scheme.Modules.pushforward
            (Stacks.AffineCotangentSheaf.specRestriction hUle)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (affineCotangentComparison f hU' e') :=
  ⟨fun j => by
    rw [Stacks.AffineCotangentSheaf.affineCotangentComparison_f, Equiv.apply_symm_apply],
    isIso_Q_map_affineCotangentComparison f hU hV e,
    fun hU' _ e' hUle hVle =>
      Stacks.AffineCotangentSheaf.affineCotangentComparison_restriction f hU hU' e e' hUle hVle⟩

end AlgebraicGeometry.Scheme.Hom

end

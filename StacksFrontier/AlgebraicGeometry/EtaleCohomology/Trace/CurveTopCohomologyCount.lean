module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyCoverCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveSmoothConnected
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelCoinvariantsLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ClosedPointEvaluation
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteGSetCover
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint

/-!
# The count `#H²_c(U_k̄, ℱ_{ρ,n}) ≤ #((ℤ/ℓⁿ)^r)_{π₁(U_k̄)}`

Let `U` be a smooth geometrically connected curve over a finite field `k`, `x̄` a geometric point,
`τ : π₁(U, x̄) → GL_r(ℚ_ℓ)` continuous with integral model `ρ`, and `ℓ` different from the
characteristic of `k`. Then for every level `n`

`#H²_c(U_k̄, ℱ_{ρ mod ℓ^{n+1}}) ≤ #((ℤ/ℓ^{n+1})^r)_{π₁(U_k̄)}`,

the coinvariants being those of the geometric fundamental group `ker(π₁(U, x̄) → π₁(Spec k))`.
This is the half of [Stacks, Tag 03VK] that bounds `H²_c` by the coinvariants.

The proof follows the source. Let `N` be an open normal subgroup of `π₁(U, x̄)` acting trivially on
`M = (ℤ/ℓ^{n+1})^r`, and `V₀ ⟶ U` the connected Galois cover with group `π₁/N`
(`AlgebraicGeometry.exists_finiteEtaleOver_fiber_equiv`). Let `L` be the residue field of a closed
point of `V₀`, finite over `k` (`AlgebraicGeometry.finite_residueFieldOverBase`), so that
`V₀ ×_k L` has an `L`-point; its connected component `V` through it is a connected Galois cover of
`W = U ×_k L`, geometrically irreducible over `L`
(`AlgebraicGeometry.geometricallyIrreducible_of_isCurve_of_section`). Then
`H²_c(U_k̄, ℱ_M) = H²_c(W_k̄, ℱ_{M|π₁(W)})` (Tags 03S6, 0DV6:
`Stacks.EtaleCohomology.compactSupportSheafCohomologyFieldExtensionIso`,
`Stacks.EtaleCohomology.nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso`), which the count on
geometrically irreducible Galois covers
(`finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_of_cover`) bounds by
the coinvariants of the image of `π₁(W)`; that image contains the geometric fundamental group
(`AlgebraicGeometry.ker_le_range_etaleFundamentalGroupMap_fieldExtension`).

The statements live in the standard model `HasDerivedCategory.standard` of the derived category, in
which `Stacks.EtaleCohomology.compactSupportSheafCohomology` is defined.

## Main results

* `AlgebraicGeometry.exists_fieldExtension_section`: a finite étale cover of a scheme of finite
  type over `k` acquires a rational point over a finite extension of `k`.
* `AlgebraicGeometry.stabilizer_eq_comap_of_mono`: stabilizers in a sub-cover of a pulled back
  Galois cover.
* `finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_coinvariants` and
  `natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_coinvariants`: `H²_c(U_k̄, ℱ_M)`
  is finite and `#H²_c(U_k̄, ℱ_M) ≤ #M_{π₁(U_k̄)}` for every finite continuous `ℤ/m`-module `M`.
* `LAdicSheaf.natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule_le`: the
  same for the levels of `ℱ_τ`, in the form consumed by
  `Stacks.EtaleCohomology.LAdicSheaf.exists_linearEquiv_coinvariants_of_levels`, and
  `LAdicSheaf.finite_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule`: the levels
  are finite.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section Section

variable {k : Type u} [Field k] {U : Scheme.{u}} (f : U ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] (V₀ : FiniteEtaleOver U) [Nonempty V₀.left]

/-- **A finite étale cover of a scheme of finite type over a field acquires a rational point over a
finite extension**: the residue field `L` of a closed point of `V₀` is finite over `k`
(Nullstellensatz), and the point gives an `L`-point of `V₀ ×_k L`. -/
theorem exists_fieldExtension_section :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
      (σ : Spec (.of L) ⟶ pullback V₀.hom (pullback.fst f (specAlgebraMap k L))),
      σ ≫ pullback.snd V₀.hom (pullback.fst f (specAlgebraMap k L)) ≫
        pullback.snd f (specAlgebraMap k L) = 𝟙 _ := by
  let g₀ := V₀.hom ≫ f
  have : CompactSpace V₀.left := (quasiCompact_iff_compactSpace g₀).mp inferInstance
  obtain ⟨v, -, hv⟩ :=
    IsClosed.exists_closed_singleton (X := V₀.left) isClosed_univ Set.univ_nonempty
  let : Algebra k (V₀.left.residueField v) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g₀.appTop ≫ V₀.left.Γevaluation v).hom.toAlgebra
  have : Module.Finite k (V₀.left.residueField v) := finite_residueFieldOverBase k g₀ v hv
  have h₁ : (V₀.left.fromSpecResidueField v ≫ V₀.hom) ≫ f =
      𝟙 _ ≫ specAlgebraMap k (V₀.left.residueField v) := by
    rw [Category.id_comp, Category.assoc]
    exact (SpecMap_algebraMap_residueField g₀ v).symm
  refine ⟨V₀.left.residueField v, inferInstance, inferInstance, inferInstance,
    pullback.lift (V₀.left.fromSpecResidueField v)
      (pullback.lift (V₀.left.fromSpecResidueField v ≫ V₀.hom) (𝟙 _) h₁)
      (pullback.lift_fst _ _ _).symm, ?_⟩
  rw [pullback.lift_snd_assoc, pullback.lift_snd]

end Section

/-- **A connected finite étale cover has a nonempty geometric fibre.** -/
theorem nonempty_finiteEtaleFiber_of_connectedSpace_left {S : Scheme.{u}} [ConnectedSpace S]
    (s : GeometricPoint S) (T : FiniteEtaleOver S) [ConnectedSpace T.left] :
    Nonempty ((finiteEtaleFiberFunctor s).obj T) := by
  have : PreGaloisCategory.IsConnected T := (isConnected_iff_connectedSpace_left T).2 ‹_›
  let _ : IsGaloisCategory (setValuedFiberFunctor (finiteEtaleFiberFintypeFunctor S s)) :=
    Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor s
  let : CategoryTheory.GaloisCategory (FiniteEtaleOver S) :=
    IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor (finiteEtaleFiberFintypeFunctor S s))
  let : PreGaloisCategory.FiberFunctor (finiteEtaleFiberFintypeFunctor S s) :=
    IsGaloisCategory.fiberFunctor _
  exact PreGaloisCategory.nonempty_fiber_of_isConnected (finiteEtaleFiberFintypeFunctor S s) T

/-- **The stabilizers of a sub-cover of a pulled back Galois cover**: if every point of the fibre
of `V₀` over `Y` has stabilizer `N`, then a point of the fibre of a cover `T` of `X` mapping
monomorphically to `V₀ ×_Y X` has stabilizer the preimage of `N` in `π₁(X)`. -/
theorem stabilizer_eq_comap_of_mono {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (g : X ⟶ Y) (y : GeometricPoint X) (V₀ : FiniteEtaleOver Y)
    (N : Subgroup (EtaleFundamentalGroup Y (y.map g)))
    (hV₀ : ∀ v : (finiteEtaleFiberFunctor (y.map g)).obj V₀,
      MulAction.stabilizer (EtaleFundamentalGroup Y (y.map g)) v = N)
    {T : FiniteEtaleOver X} (ι : T ⟶ (finiteEtaleBaseChange g).obj V₀) [Mono ι.left]
    (t : (finiteEtaleFiberFunctor y).obj T) :
    MulAction.stabilizer (EtaleFundamentalGroup X y) t =
      N.comap (etaleFundamentalGroupMap g y).toMonoidHom := by
  have hinj : Function.Injective ((finiteEtaleFiberFunctor y).map ι) := fun a b h =>
    Subtype.ext ((cancel_mono ι.left).1 (congrArg Subtype.val h))
  ext w
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, ← hV₀
    (finiteEtaleFiberProjection g y V₀ ((finiteEtaleFiberFunctor y).map ι t)),
    MulAction.mem_stabilizer_iff]
  have hnat : (finiteEtaleFiberFunctor y).map ι (w • t) =
      w • (finiteEtaleFiberFunctor y).map ι t :=
    (ConcreteCategory.congr_hom (w.asIso.hom.naturality ι) t).symm
  have hproj := etaleFundamentalGroupMap_finiteEtaleFiberProjection g y V₀ w
    ((finiteEtaleFiberFunctor y).map ι t)
  constructor
  · intro h
    calc _ = finiteEtaleFiberProjection g y V₀ (w • (finiteEtaleFiberFunctor y).map ι t) :=
          hproj.symm
      _ = finiteEtaleFiberProjection g y V₀ ((finiteEtaleFiberFunctor y).map ι (w • t)) := by
          rw [hnat]
      _ = _ := by rw [h]
  · intro h
    exact hinj (hnat.trans ((finiteEtaleFiberProjectionEquiv g y V₀).injective (hproj.trans h)))

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- **Coinvariants and surjections**: a surjection `V₁ → V₂` compatible with the coinvariant
relations of `ρ₂` bounds the coinvariants of `ρ₂` by those of `ρ₁`. -/
private theorem natCard_coinvariants_le_of_surjective {R G₁ G₂ V₁ V₂ : Type*} [CommRing R]
    [Group G₁] [Group G₂] [AddCommGroup V₁] [Module R V₁] [AddCommGroup V₂] [Module R V₂]
    [Finite V₁] (ρ₁ : Representation R G₁ V₁) (ρ₂ : Representation R G₂ V₂) (f : V₁ →ₗ[R] V₂)
    (hf : Function.Surjective f)
    (h : ∀ g v, Representation.Coinvariants.mk ρ₂ (f (ρ₁ g v)) =
      Representation.Coinvariants.mk ρ₂ (f v)) :
    Nat.card (Representation.Coinvariants ρ₂) ≤ Nat.card (Representation.Coinvariants ρ₁) := by
  have : Finite (Representation.Coinvariants ρ₁) :=
    Finite.of_surjective _ (Representation.Coinvariants.mk_surjective _)
  refine Nat.card_le_card_of_surjective
    (Representation.Coinvariants.lift ρ₁ (Representation.Coinvariants.mk ρ₂ ∘ₗ f)
      fun g => LinearMap.ext (h g)) fun c => ?_
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ c
  obtain ⟨w, rfl⟩ := hf v
  exact ⟨Representation.Coinvariants.mk _ w, rfl⟩

section Coinvariants

variable {R : Type*} [CommRing R] {G H : Type*} [Group G] [Group H] (φ : H →* G)
  {V : Type*} [AddCommGroup V] [Module R V] [Finite V] (σ : Representation R G V)

/-- **Coinvariants of a larger group are a quotient**: if `K ≤ φ(H)`, the coinvariants of `H`
acting through `φ` are a quotient of those of `K`. -/
theorem natCard_coinvariants_comp_le_of_le_range (K : Subgroup G) (hK : K ≤ φ.range) :
    Nat.card (Representation.Coinvariants (σ.comp φ)) ≤
      Nat.card (Representation.Coinvariants (σ.comp K.subtype)) := by
  have : Finite (Representation.Coinvariants (σ.comp K.subtype)) :=
    Finite.of_surjective _ (Representation.Coinvariants.mk_surjective _)
  refine natCard_coinvariants_le_of_surjective _ _ LinearMap.id Function.surjective_id
    fun h v => ?_
  obtain ⟨w, hw⟩ := hK h.2
  change Representation.Coinvariants.mk (σ.comp φ) (σ h.1 v) =
    Representation.Coinvariants.mk (σ.comp φ) v
  rw [← hw]
  exact Representation.Coinvariants.mk_self_apply (σ.comp φ) w v

end Coinvariants

section Count

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1]
  {k : Type u} [Field k] [Finite k] (f : U.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsCurve k f] [Smooth f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] [CharP k p]

include p in
/-- **The count after the base change to `L`**, with all the data of the reduction given: `V₀` a
Galois cover of `U` trivializing `M` (stabilizers `N`), `L` a finite extension of `k` inside `k̄`
and `V` a connected clopen of `V₀ ×_k L` geometrically irreducible over `L`, with a geometric point
over `z`. -/
theorem finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_of_fieldExtension
    (hm : IsUnit (m : kbar)) (hUgi : GeometricallyConnected f)
    (z : GeometricPoint U.1) [CompactSpace (EtaleFundamentalGroup U.1 z)]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 z))
    (N : Subgroup (EtaleFundamentalGroup U.1 z)) [N.Normal]
    (hM : ∀ s ∈ N, M.obj.obj.obj.ρ s = 1) (V₀ : FiniteEtaleOver U.1)
    (hV₀ : ∀ v : (finiteEtaleFiberFunctor z).obj V₀,
      MulAction.stabilizer (EtaleFundamentalGroup U.1 z) v = N)
    (L : Type u) [Field L] [Finite L] [Algebra k L] [Module.Finite k L] [Algebra L kbar]
    [IsScalarTower k L kbar] {Vs : Scheme.{u}} [ConnectedSpace Vs]
    (ι : Vs ⟶ pullback V₀.hom (pullback.fst f (specAlgebraMap k L))) [IsOpenImmersion ι]
    [IsClosedImmersion ι]
    (hgi : GeometricallyIrreducible
      ((ι ≫ pullback.snd V₀.hom (pullback.fst f (specAlgebraMap k L))) ≫
        pullback.snd f (specAlgebraMap k L)))
    (yV : GeometricPoint Vs)
    (hy : (yV.map (ι ≫ pullback.snd V₀.hom (pullback.fst f (specAlgebraMap k L)))).map
      (pullback.fst f (specAlgebraMap k L)) = z) :
    Finite ((compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U z (ZMod m)).obj M)) ∧
    Nat.card ((compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U z (ZMod m)).obj M)) ≤
      Nat.card (Representation.Coinvariants
        ((finiteTypeContinuousModuleRepresentation (ZMod m) _ M).comp
          (etaleFundamentalGroupMap f z).toMonoidHom.ker.subtype)) := by
  subst hy
  classical
  let : Fintype L := Fintype.ofFinite L
  -- the base change `W = U ×_k L`
  let s := specAlgebraMap k L
  have : IsFinite s := (IsFinite.SpecMap_iff _).2 ((RingHom.finite_algebraMap).2 inferInstance)
  have : Etale s := etale_specMap_algebraMap_of_finite_separable k L
  have hs : finiteEtale s := ⟨inferInstance, inferInstance⟩
  have hfst : finiteEtale (pullback.fst f s) := ⟨inferInstance, inferInstance⟩
  let W : B.Scheme := fieldExtensionScheme B U f L
  let gW : W ⟶ U := fieldExtensionProj B U f L
  let fW := pullback.snd f s
  have : ConnectedSpace W.1 :=
    hUgi.geometrically_connectedSpace s (pullback.fst f s) (pullback.snd f s)
      (IsPullback.of_hasPullback f s)
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_geometricallyConnected_of_smooth f hUgi
  have : IsCurve L fW := isCurve_pullback_snd k L f
  have hWgi : GeometricallyIrreducible fW := inferInstance
  -- the cover `V ⟶ W`
  let gV := ι ≫ pullback.snd V₀.hom (pullback.fst f s)
  have : IsFinite gV := inferInstance
  have : Etale gV := inferInstance
  let Vb : B.Scheme :=
    ⟨Vs, Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (gV ≫ pullback.fst f s) U.property⟩
  let g : Vb ⟶ W := ObjectProperty.homMk gV
  have : IsFinite (B.inclusion.map g) := inferInstanceAs (IsFinite gV)
  have : Etale (B.inclusion.map g) := inferInstanceAs (Etale gV)
  have : ConnectedSpace Vb.1 := inferInstanceAs (ConnectedSpace Vs)
  have hg : finiteEtale g.hom := ⟨inferInstanceAs (IsFinite gV), inferInstanceAs (Etale gV)⟩
  let y' : GeometricPoint W.1 := yV.map g.hom
  -- `H²_c(U_k̄, ℱ_M) = H²_c(W_k̄, ℱ_{M|π₁(W)})`
  let φ := etaleFundamentalGroupMap gW.hom y'
  let Mres := (finiteTypeContinuousModuleRes (ZMod m) φ).obj M
  obtain ⟨e₂⟩ := nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso B gW y' (ZMod m) M
  let e₁ := (compactSupportSheafCohomologyFieldExtensionIso (ZMod m) f j L kbar 2).app
    ((lisseEtaleSheaf B U (y'.map gW.hom) (ZMod m)).obj M)
  let eqv : (compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
      ((lisseEtaleSheaf B U (y'.map gW.hom) (ZMod m)).obj M) ≃
      (compactSupportSheafCohomology (ZMod m) fW (compactificationFieldBaseChange f j L)
        kbar 2).obj ((lisseEtaleSheaf B W y' (ZMod m)).obj Mres) :=
    (e₁ ≪≫ (compactSupportSheafCohomology (ZMod m) fW
      (compactificationFieldBaseChange f j L) kbar 2).mapIso e₂).toLinearEquiv.toEquiv
  -- the count on `W`
  have : CharP L p := (Algebra.charP_iff k L p).1 inferInstance
  obtain ⟨q', -, hq'⟩ := FiniteField.card L p
  have : ∀ Y, Finite ((finiteEtaleFiberFunctor y').obj Y) := finite_finiteEtaleFiber y'
  let ιc : finiteEtaleOverSource hg ⟶ (finiteEtaleBaseChange gW.hom).obj V₀ :=
    MorphismProperty.Over.homMk ι rfl trivial
  have : Mono ιc.left := inferInstanceAs (Mono ι)
  have hstab := stabilizer_eq_comap_of_mono gW.hom y' V₀ N hV₀ ιc
    (finiteEtaleOverSourcePoint hg yV)
  have hN : (MulAction.stabilizer (EtaleFundamentalGroup W.1 (yV.map g.hom))
      (finiteEtaleOverSourcePoint hg yV)).Normal :=
    hstab ▸ Subgroup.Normal.comap inferInstance _
  have hMres : ∀ s' ∈ MulAction.stabilizer (EtaleFundamentalGroup W.1 (yV.map g.hom))
      (finiteEtaleOverSourcePoint hg yV), ∀ v, (Mres.obj.obj.obj.ρ s').asHom.hom v = v := by
    intro s' hs' v
    rw [hstab] at hs'
    exact congrArg (fun F => F.asHom.hom v) (hM _ hs')
  have hGC := finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_of_cover B W
    fW (compactificationFieldBaseChange f j L) kbar m p q' hq' hm hWgi g yV hgi hg hN Mres hMres
  -- the coinvariants of `π₁(W)` are a quotient of those of the geometric fundamental group
  have hker := ker_le_range_etaleFundamentalGroupMap_fieldExtension f L hs y' hfst
  have : Finite M.obj.obj.obj.V := (moduleCat_isFG_iff_finite (ZMod m) _).1 M.property
  have hσ : finiteTypeContinuousModuleRepresentation (ZMod m) _ Mres =
      (finiteTypeContinuousModuleRepresentation (ZMod m) _ M).comp φ.toMonoidHom := rfl
  have hco := natCard_coinvariants_comp_le_of_le_range φ.toMonoidHom
    (finiteTypeContinuousModuleRepresentation (ZMod m) _ M) _ hker
  rw [← hσ] at hco
  have := hGC.1
  exact ⟨Finite.of_equiv _ eqv.symm, (Nat.card_congr eqv).le.trans (hGC.2.trans hco)⟩

include p in
/-- **`#H²_c(U_k̄, ℱ_M) ≤ #M_{π₁(U_k̄)}`** for every finite `ℤ/m`-module `M` with a continuous
action of `π₁(U, z̄)`, on a smooth geometrically connected curve `U` over a finite field and for
`m` invertible in `k̄`; the coinvariants are those of the geometric fundamental group
`ker(π₁(U, z̄) → π₁(Spec k))`. -/
theorem finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_coinvariants
    (hm : IsUnit (m : kbar)) (hUgi : GeometricallyConnected f)
    (z : GeometricPoint U.1) [CompactSpace (EtaleFundamentalGroup U.1 z)]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 z)) :
    Finite ((compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U z (ZMod m)).obj M)) ∧
    Nat.card ((compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U z (ZMod m)).obj M)) ≤
      Nat.card (Representation.Coinvariants
        ((finiteTypeContinuousModuleRepresentation (ZMod m) _ M).comp
          (etaleFundamentalGroupMap f z).toMonoidHom.ker.subtype)) := by
  classical
  -- an open normal subgroup acting trivially, and the Galois cover it defines
  obtain ⟨N, hNn, hNo, hNM⟩ := exists_isOpen_normal_subgroup_ρ_eq_one_finiteType (ZMod m)
    (EtaleFundamentalGroup U.1 z) M
  have := hNn
  have : Finite (EtaleFundamentalGroup U.1 z ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  obtain ⟨V₀, e, he⟩ :=
    AlgebraicGeometry.exists_finiteEtaleOver_fiber_equiv z (EtaleFundamentalGroup U.1 z ⧸ N)
    (AlgebraicGeometry.isOpen_stabilizer_quotient z N hNo)
  have hV₀ : ∀ v : (finiteEtaleFiberFunctor z).obj V₀,
      MulAction.stabilizer (EtaleFundamentalGroup U.1 z) v = N := by
    intro v
    ext w
    rw [MulAction.mem_stabilizer_iff]
    obtain ⟨c, rfl⟩ := e.symm.surjective v
    induction c using QuotientGroup.induction_on with | H g => ?_
    rw [← e.injective.eq_iff, he, Equiv.apply_symm_apply,
      show w • (QuotientGroup.mk g : EtaleFundamentalGroup U.1 z ⧸ N) = QuotientGroup.mk (w * g)
        from rfl, QuotientGroup.eq]
    simp only [mul_inv_rev]
    constructor
    · intro h
      have h₂ : w⁻¹ ∈ N := by simpa [mul_assoc] using hNn.conj_mem _ h g
      simpa using N.inv_mem h₂
    · intro h
      simpa [mul_assoc] using hNn.conj_mem _ (N.inv_mem h) g⁻¹
  have : ConnectedSpace V₀.left := by
    refine connectedSpace_left_of_exists_smul_eq (y := e.symm (QuotientGroup.mk 1)) fun v => ?_
    obtain ⟨c, rfl⟩ := e.symm.surjective v
    induction c using QuotientGroup.induction_on with | H g => ?_
    refine ⟨g, e.injective ?_⟩
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact congrArg QuotientGroup.mk (mul_one g)
  have : Nonempty V₀.left := ConnectedSpace.toNonempty
  -- a finite extension `L` of `k` over which `V₀` has a rational point
  obtain ⟨L, _, _, _, σ₀, hσ₀⟩ := AlgebraicGeometry.exists_fieldExtension_section f V₀
  have : Finite L := Module.finite_of_finite k
  let ψ : L →ₐ[k] kbar := IsAlgClosed.lift
  let : Algebra L kbar := ψ.toRingHom.toAlgebra
  have : IsScalarTower k L kbar := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  let s := specAlgebraMap k L
  have : IsFinite s := (IsFinite.SpecMap_iff _).2 ((RingHom.finite_algebraMap).2 inferInstance)
  have : Etale s := etale_specMap_algebraMap_of_finite_separable k L
  let P := pullback V₀.hom (pullback.fst f s)
  -- the connected component `V` of `V₀ ×_k L` through the rational point
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_geometricallyConnected_of_smooth f hUgi
  have : IsCurve L (pullback.snd f s) := isCurve_pullback_snd k L f
  have : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd V₀.hom (pullback.fst f s) ≫ pullback.snd f s)
  let pt : P := σ₀.base (Classical.arbitrary _)
  let O : P.Opens :=
    ⟨connectedComponent pt, Stacks.Chow.isOpen_connectedComponent_of_isLocallyNoetherian pt⟩
  have : IsClosedImmersion O.ι :=
    IsClosedImmersion.of_isPreimmersion O.ι (O.range_ι ▸ isClosed_connectedComponent)
  have : ConnectedSpace O :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hσO : Set.range σ₀.base ⊆ Set.range O.ι.base := by
    rw [O.range_ι]
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a (Classical.arbitrary _)]
    exact mem_connectedComponent
  let σ : Spec (.of L) ⟶ O := IsOpenImmersion.lift O.ι σ₀ hσO
  have hσ : σ ≫ (O.ι ≫ pullback.snd V₀.hom (pullback.fst f s)) ≫ pullback.snd f s = 𝟙 _ := by
    rwa [← Category.assoc, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc]
  have : IsCurve L ((O.ι ≫ pullback.snd V₀.hom (pullback.fst f s)) ≫ pullback.snd f s) :=
    isCurve_comp_of_isFinite_of_etale L (pullback.snd f s)
      (O.ι ≫ pullback.snd V₀.hom (pullback.fst f s))
  have hgi : GeometricallyIrreducible
      ((O.ι ≫ pullback.snd V₀.hom (pullback.fst f s)) ≫ pullback.snd f s) :=
    geometricallyIrreducible_of_geometricallyConnected_of_smooth _
      (geometricallyConnected_of_connectedSpace_of_section _ σ hσ)
  -- a geometric point of `V` over `z`
  have hcomp : finiteEtale ((O.ι ≫ pullback.snd V₀.hom (pullback.fst f s)) ≫ pullback.fst f s) :=
    ⟨inferInstance, inferInstance⟩
  have : ConnectedSpace (finiteEtaleOverSource hcomp).left := inferInstanceAs (ConnectedSpace O)
  obtain ⟨q⟩ := AlgebraicGeometry.nonempty_finiteEtaleFiber_of_connectedSpace_left z
    (finiteEtaleOverSource hcomp)
  let yV : GeometricPoint O := ⟨z.residueField, q.1⟩
  have hy : (yV.map (O.ι ≫ pullback.snd V₀.hom (pullback.fst f s))).map (pullback.fst f s) = z := by
    have hq : q.1 ≫ ((O.ι ≫ pullback.snd V₀.hom (pullback.fst f s)) ≫ pullback.fst f s) = z.hom :=
      q.2
    change (⟨z.residueField, (q.1 ≫ O.ι ≫ pullback.snd V₀.hom (pullback.fst f s)) ≫
      pullback.fst f s⟩ : GeometricPoint U.1) = z
    simp only [Category.assoc] at hq ⊢
    rw [hq]
  exact finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_of_fieldExtension B
    U f j kbar m p hm hUgi z M N hNM V₀ hV₀ L O.ι hgi yV hy

include p in
/-- **`#H²_c(U_k̄, ℱ_M) ≤ #M_{π₁(U_k̄)}`**, the bound of
`finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_coinvariants`. -/
theorem natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_coinvariants
    (hm : IsUnit (m : kbar)) (hUgi : GeometricallyConnected f)
    (z : GeometricPoint U.1) [CompactSpace (EtaleFundamentalGroup U.1 z)]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 z)) :
    Nat.card ((compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U z (ZMod m)).obj M)) ≤
      Nat.card (Representation.Coinvariants
        ((finiteTypeContinuousModuleRepresentation (ZMod m) _ M).comp
          (etaleFundamentalGroupMap f z).toMonoidHom.ker.subtype)) :=
  (finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_coinvariants B U f j kbar
    m p hm hUgi z M).2

end Count

/-! ### The levels of `ℱ_τ` -/

section Levels

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime] [ConnectedSpace U.1]
  {k : Type u} [Field k] [Finite k] (f : U.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]
  [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
  (p : ℕ) [Fact p.Prime] [CharP k p] (x : GeometricPoint U.1) {r : ℕ}
  (τ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ)
  [CompactSpace (EtaleFundamentalGroup U.1 x)]

/-- **`#H²_c(U_k̄, ℱ_{ρ,n+1}) ≤ #((ℤ/ℓ^{n+1})^r)_{π₁(U_k̄)}`** ([Stacks, Tag 03VK], the bound by
the coinvariants): for a smooth geometrically connected curve `U` over a finite field `k` of
characteristic `p ≠ ℓ`, a continuous `τ : π₁(U, x̄) → GL_r(ℚ_ℓ)` with integral model `ρ`, and every
level `n`, the top compactly supported cohomology of the lisse sheaf of `ρ mod ℓ^{n+1}` has at most
as many elements as the coinvariants of the geometric fundamental group, and is finite. -/
theorem
    LAdicSheaf.finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule_le
    (hℓ : ℓ ≠ p) (n : ℕ) :
    Finite ((compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
            (n + 1)))) ∧
    Nat.card ((compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
            (n + 1)))) ≤
      Nat.card (levelCoinvariants (etaleFundamentalGroupMap f x).toMonoidHom.ker
        (integralModel τ hτ) (n + 1)) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurve k f := isCurve_of_smoothOfRelativeDimension_one_of_connectedSpace f
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have hUgi : GeometricallyConnected f :=
    (geometricallyConnected_iff_connectedSpace_baseChange k kbar f).2 ‹_›
  have : CharP kbar p := (Algebra.charP_iff k kbar p).1 inferInstance
  have hm : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar) := by
    refine IsUnit.mk0 _ ?_
    rw [Nat.cast_pow]
    refine pow_ne_zero _ fun h => hℓ ?_
    rw [CharP.cast_eq_zero_iff kbar p] at h
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 h).symm
  let ρ := integralModel τ hτ
  let M := levelModule.{u + 1, u + 1} ρ (continuous_integralModel τ hτ) (n + 1)
  let H := (etaleFundamentalGroupMap f x).toMonoidHom.ker
  have h := finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_le_coinvariants B U
    f j kbar (ℓ ^ (n + 1)) p hm hUgi x M
  let σM := finiteTypeContinuousModuleRepresentation (ZMod (ℓ ^ (n + 1))) _ M
  exact ⟨h.1, h.2.trans (natCard_coinvariants_le_of_surjective _ _
    (ULift.moduleEquiv (R := ZMod (ℓ ^ (n + 1)))).symm.toLinearMap
    (ULift.moduleEquiv (R := ZMod (ℓ ^ (n + 1)))).symm.surjective fun g v =>
      Representation.Coinvariants.mk_self_apply (σM.comp H.subtype) g (ULift.up v))⟩

/-- **`#H²_c(U_k̄, ℱ_{ρ,n+1}) ≤ #((ℤ/ℓ^{n+1})^r)_{π₁(U_k̄)}`** ([Stacks, Tag 03VK], the bound by
the coinvariants), the bound of
`finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule_le`. -/
theorem LAdicSheaf.natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule_le
    (hℓ : ℓ ≠ p) (n : ℕ) :
    Nat.card ((compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
            (n + 1)))) ≤
      Nat.card (levelCoinvariants (etaleFundamentalGroupMap f x).toMonoidHom.ker
        (integralModel τ hτ) (n + 1)) :=
  (LAdicSheaf.finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule_le
    B U ℓ f j kbar p x τ hτ hℓ n).2

/-- **`H²_c(U_k̄, ℱ_{ρ,n+1})` is finite**: it is a quotient of the level coinvariants. -/
theorem LAdicSheaf.finite_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule
    (hℓ : ℓ ≠ p) (n : ℕ) :
    Finite ((compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
            (n + 1)))) :=
  (LAdicSheaf.finite_and_natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule_le
    B U ℓ f j kbar p x τ hτ hℓ n).1

end Levels

end Stacks.EtaleCohomology

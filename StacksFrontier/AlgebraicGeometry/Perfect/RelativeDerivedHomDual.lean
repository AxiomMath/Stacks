module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentHocolim
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualBounds
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTensorPullbackBound
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityPairingCupProduct

/-!
# Relative derived internal Hom into a relatively perfect object

Let `f : X ⟶ S` be proper, flat and of finite presentation over a quasi-compact and
quasi-separated `S`, let `E ∈ D(𝒪_X)` be `S`-perfect and `K ∈ D(𝒪_X)` pseudo-coherent.
[Stacks, Tag 0DJU] produces a pseudo-coherent `L ∈ D(𝒪_S)` with
`Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_S)`, compatibly with arbitrary base change.

The proof is the one of the source. Write `K = hocolim Kₙ` with `Kₙ` perfect and `Kₙ ⟶ K` an
isomorphism on `Hⁱ` for `i ≥ -n` ([Stacks, Tag 0DJN]). The objects `Mₙ = Rf_* R𝓗om(Kₙ, E)` are
perfect ([Stacks, Tags 0DI4 and 0DJT]), `L = hocolim Mₙ^∨`, and the formula is
`Rf_* R𝓗om(K, E) = R lim Mₙ = R𝓗om(L, 𝒪_S)` ([Stacks, Tag 0DJI], biduality), proved in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore` together with its base-changed
form ([Stacks, Tags 08I3, 0GM7 and 08HY]). Pseudo-coherence of `L` follows from the bounds of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualBounds`: the transition maps of
`(Mₙ^∨)` are isomorphisms in degrees `≥ -n - a + 1`, `a` being a lower bound for `E` relative to
`S`, so the coprojections `Mₙ^∨ ⟶ L` are isomorphisms there ([Stacks, Tag 0CRK]) and
[Stacks, Tag 0DJN] concludes. Where the source bounds the cone of `Mₙ^∨ ⟶ Mₙ₊₁^∨` through its
fibres and [Stacks, Tag 0BCD], this development uses the argument of the proof of
[Stacks, Tag 08IF]: morphisms out of that cone into a quasi-coherent module placed in a single
degree vanish, by the projection formula ([Stacks, Tag 08EU]) and the duality of perfect
objects, and the top cohomology of a bounded above object admits such a nonzero morphism.

## Main results

* `exists_construction_isPseudoCoherent`: the data `Kₙ`, `Mₙ`, `L` of the proof with their
  properties.
* `exists_isPseudoCoherent_pushforward_sheafHom_iso`: **[Stacks, Tag 0DJU]**.

## Implementation notes

The derived categories are read at the standard model `CategoryTheory.HasDerivedCategory.standard`,
named through the abbreviations of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore` (`DStd`, `pushStd`, `pullStd`,
`HStd`, …): every input of the proof is stated at that model.

## References

* [Stacks Project, Tag 0DJU](https://stacks.math.columbia.edu/tag/0DJU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry Stacks.SheafOfModules

universe u

namespace Stacks.AlgebraicGeometry.RelativeDerivedHomDual

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 0DI4], second assertion, for an internal Hom out of a perfect object**:
`R𝓗om(P, E) = P^∨ ⊗^L E` is `S`-perfect for `P` perfect and `E` `S`-perfect. -/
theorem isRelPerfect_sheafHom [Flat f] [LocallyOfFinitePresentation f] (P E : DStd X)
    (hP : IsPerfectSite P) (hE : IsRelPerfect f E) :
    IsRelPerfect f (((derivedSheafHom X.sheaf).obj (op P)).obj E) :=
  isRelativelyPerfect_of_iso f (sheafHomIsoDualTensor P E hP).symm
    (Scheme.Hom.isPerfectRelativeTo_canonical_derivedTensor f (derivedDual X.sheaf P) E
      (isPerfect_ringedSpace_of_isPerfectSite (isPerfect_derivedDual X.sheaf P hP)) hE)

/-- **[Stacks, Tag 0DJT] at the standard model**: for `f` flat, proper and of finite
presentation, `Rf_*` of an `S`-perfect object is perfect. -/
theorem isPerfectSite_pushStd [Flat f] [IsProper f] [LocallyOfFinitePresentation f] (E : DStd X)
    (hE : IsRelPerfect f E) : IsPerfectSite ((pushStd f).obj E) :=
  isPerfectSite_of_isPerfect_ringedSpace
    (RelativelyPerfectProperPushforward.isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_flat
      f E hE)

/-- **[Stacks, Tag 0DJT], base change, at the standard model**: for `f` flat, proper and of
finite presentation, `E` `S`-perfect and a cartesian square, the base change map
`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is invertible. -/
theorem isIso_derivedBaseChangeSquare_app [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : DStd X) (hE : IsRelPerfect f E) {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S')
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g) :
    IsIso ((Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
      (comp_toShHom_of_comm sq.w)).app E) :=
  (RelativelyPerfectProperPushforward.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap
    f E hE).2 g f' g' sq

/-- **[Stacks, Tag 0DJN], (1) ⟹ (2), at the standard model**: on a quasi-compact and
quasi-separated scheme a pseudo-coherent `K` is a derived colimit of perfect objects `Kₙ` whose
coprojections `Kₙ ⟶ K` are isomorphisms on cohomology in degrees `≥ -n`. -/
theorem exists_perfect_system_of_isPseudoCoherent [CompactSpace X] [QuasiSeparatedSpace X]
    (K : DStd X) (hK : IsPseudoCoherentStd K) :
    ∃ (F : ℕ ⥤ DStd X) (c : ∀ n, F.obj n ⟶ K), (∀ n, IsPerfectSite (F.obj n)) ∧
      IsHomotopyColimitWith F K c ∧
        ∀ (n : ℕ) (i : ℤ), -(n : ℤ) ≤ i → IsIso ((HStd X i).map (c n)) := by
  obtain ⟨F, _, c, hF, -, hFK, htr⟩ :=
    @Stacks.PseudoCoherentHocolim.exists_perfect_hocolim_of_isPseudoCoherent_of_supportedOn X
      (HasDerivedCategory.standard _) _ _ Set.univ isClosed_univ (by simp) K
      (fun _ x hx => absurd (Set.mem_univ x) hx) hK
  exact ⟨F, c, fun n => isPerfectSite_of_isPerfect_ringedSpace (hF n), hFK,
    fun n i hi => (@Stacks.PseudoCoherentHocolim.isIso_truncGE_map_iff _ _ _
      (HasDerivedCategory.standard _) _ _ (c n) _).1 (htr n) i hi⟩

/-! ### Cohomology of a derived colimit -/

/-- Colimits over `ℕ` of `𝒪_X`-modules exist and are exact. -/
instance instHasExactColimitsOfShapeNat (X : Scheme.{u}) :
    HasExactColimitsOfShape ℕ (StructureSheafModules X.sheaf) :=
  Stacks.PseudoCoherentHocolim.hasExactColimitsOfShape_nat_modules X

/-- The cohomology sheaves commute with direct sums indexed by `ℕ`, at the standard model. -/
instance instPreservesColimitsOfShapeHStd (X : Scheme.{u}) (i : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ) (HStd X i) :=
  @Stacks.PseudoCoherentHocolim.preservesColimitsOfShape_discrete_nat_homologyFunctor X
    (HasDerivedCategory.standard _) i

/-- **The coprojections of a derived colimit, in a degree where the system is eventually
constant**: if `K = hocolim Kₙ` with coprojections `cₙ` and `Hⁱ(Kₖ) ⟶ Hⁱ(Kₖ₊₁)` is an
isomorphism for every `k ≥ n`, then `Hⁱ(cₙ) : Hⁱ(Kₙ) ⟶ Hⁱ(K)` is an isomorphism ([Stacks,
Tag 0CRK]). -/
theorem isIso_homology_coprojection {X : Scheme.{u}} {F : ℕ ⥤ DStd X} {K : DStd X}
    {c : ∀ n, F.obj n ⟶ K} (hK : IsHomotopyColimitWith F K c) (i : ℤ) (n : ℕ)
    (h : ∀ k, n ≤ k → IsIso ((HStd X i).map (F.map (homOfLE (Nat.le_succ k))))) :
    IsIso ((HStd X i).map (c n)) := by
  obtain ⟨p, q, hT, hc⟩ := hK
  obtain ⟨e, he⟩ := exists_iso_colimit_of_isHomotopyColimit F (HStd X i) p q hT
  have hd : ∀ d (hnd : n ≤ n + d), IsIso ((F ⋙ HStd X i).map (homOfLE hnd)) := by
    intro d
    induction d with
    | zero =>
      intro hnd
      rw [show homOfLE hnd = 𝟙 n from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
      infer_instance
    | succ d ih =>
      intro hnd
      rw [show homOfLE hnd = homOfLE (Nat.le_add_right n d) ≫ homOfLE (Nat.le_succ (n + d)) from
        Subsingleton.elim _ _, Functor.map_comp]
      exact IsIso.comp_isIso' (ih (Nat.le_add_right n d)) (h (n + d) (Nat.le_add_right n d))
  have hev : (F ⋙ HStd X i).IsEventuallyConstantFrom n := by
    intro j f
    obtain ⟨d, rfl⟩ : ∃ d, j = n + d := ⟨j - n, by have := leOfHom f; omega⟩
    rw [show f = homOfLE (Nat.le_add_right n d) from Subsingleton.elim _ _]
    exact hd d _
  have : IsIso (colimit.ι (F ⋙ HStd X i) n) :=
    hev.isIso_ι_of_isColimit (colimit.isColimit (F ⋙ HStd X i))
  have hn := he n
  rw [hc] at hn
  rw [← hn]
  infer_instance

/-! ### The construction -/

/-- A system over `ℕ` in `D(𝒪_S)` whose direct sum exists has a derived colimit with coprojections:
complete its telescope map to a distinguished triangle. -/
private theorem exists_isHomotopyColimitWith_of_hasCoproduct {S : Scheme.{u}} (G : ℕ ⥤ DStd S)
    [HasCoproduct G.obj] : ∃ (L : DStd S) (d : ∀ n, G.obj n ⟶ L), IsHomotopyColimitWith G L d := by
  obtain ⟨L, p, q, hT⟩ := distinguished_cocone_triangle (Sigma.desc fun n ↦
    Sigma.ι G.obj n - G.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι G.obj (n + 1))
  exact ⟨L, _, p, q, hT, fun _ => rfl⟩

/-- The terms `Mₙ = Rf_* R𝓗om(Fₙ, E)` of the system of internal Homs out of a system of perfect
objects into an `S`-perfect object are perfect ([Stacks, Tags 0DI4 and 0DJT]). -/
private theorem isPerfectSite_pushforwardSheafHomSystem [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] (F : ℕ ⥤ DStd X) (hF : ∀ n, IsPerfectSite (F.obj n))
    (E : DStd X) (hE : IsRelPerfect f E) (n : ℕ) :
    IsPerfectSite ((pushforwardSheafHomSystem f F E).obj (op n)) :=
  isPerfectSite_pushStd f _ (isRelPerfect_sheafHom f (F.obj n) E (hF n) hE)

/-- **The construction behind [Stacks, Tag 0DJU]**, without the pseudo-coherence of `L`.

For `f : X ⟶ S` flat, proper and of finite presentation over a quasi-compact and
quasi-separated `S`, `E` `S`-perfect and `K` pseudo-coherent:

* `K = hocolim Kₙ` with `Kₙ` perfect and `Kₙ ⟶ K` an isomorphism on `Hⁱ` for `i ≥ -n`
  ([Stacks, Tag 0DJN]);
* the terms `Mₙ = Rf_* R𝓗om(Kₙ, E)` of `pushforwardSheafHomSystem f FK E` are perfect
  ([Stacks, Tags 0DI4 and 0DJT]);
* `L = hocolim Mₙ^∨` exists, with coprojections `d`;
* `Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_S)`.

The witnesses of the two derived colimits carry the coprojections `c` and `d`. -/
theorem exists_construction [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (E K : DStd X) (hE : IsRelPerfect f E)
    (hK : IsPseudoCoherentStd K) :
    ∃ (FK : ℕ ⥤ DStd X) (_ : HasCoproduct FK.obj) (c : ∀ n, FK.obj n ⟶ K),
      IsHomotopyColimitWith FK K c ∧ (∀ n, IsPerfectSite (FK.obj n)) ∧
      (∀ (n : ℕ) (i : ℤ), -(n : ℤ) ≤ i → IsIso ((HStd X i).map (c n))) ∧
      (∀ n : ℕ, IsPerfectSite ((pushforwardSheafHomSystem f FK E).obj (op n))) ∧
      ∃ (_ : HasCoproduct (dualSystem (pushforwardSheafHomSystem f FK E)).obj) (L : DStd S)
        (d : ∀ n, (dualSystem (pushforwardSheafHomSystem f FK E)).obj n ⟶ L),
        IsHomotopyColimitWith (dualSystem (pushforwardSheafHomSystem f FK E)) L d ∧
        Nonempty ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op K)).obj E) ≅
          ((derivedSheafHom S.sheaf).obj (op L)).obj (unitObj S)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨F, c, hF, hFK, htr⟩ := exists_perfect_system_of_isPseudoCoherent K hK
  have hM := isPerfectSite_pushforwardSheafHomSystem f F hF E hE
  let Lsys := dualSystem (pushforwardSheafHomSystem f F E)
  obtain ⟨L, d, hL⟩ := exists_isHomotopyColimitWith_of_hasCoproduct Lsys
  exact ⟨F, inferInstance, c, hFK, hF, htr, hM, inferInstance, L, d, hL,
    nonempty_iso_pushforward_sheafHom f F E hFK.isHomotopyColimit (fun n => hM n.unop)
      hL.isHomotopyColimit⟩

section Assembly

open MonoidalCategory

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

/-- **The projection formula at a quasi-coherent module in a single degree** ([Stacks, Tag 08EU]):
for `f` quasi-compact and quasi-separated, `Z ∈ D(𝒪_X)` pseudo-coherent and `M` a quasi-coherent
`𝒪_S`-module, `Rf_*Z ⊗^L M[-j] ≅ Rf_*(Z ⊗^L Lf^*M[-j])`. -/
theorem nonempty_pushforward_tensor_single_iso [QuasiCompact f] [QuasiSeparated f] (Z : DStd X)
    (hZ : IsPseudoCoherentStd Z) (M : StructureSheafModules S.sheaf) (hM : M.IsQuasicoherent)
    (j : ℤ) :
    Nonempty ((pushStd f).obj Z ⊗ (singleStd S j).obj M ≅
      (pushStd f).obj (Z ⊗ (pullStd f).obj ((singleStd S j).obj M))) := by
  have hiso := Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh f Z
    ((singleStd S j).obj M)
    (fun i => @AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X (stdOXMod _) Z hZ i)
    (fun i => isQuasicoherent_homology_singleFunctor M hM j i)
  exact ⟨((derivedTensorCanonicalIso S.toRingedSpace).app ((pushStd f).obj Z)).app
      ((singleStd S j).obj M) ≪≫
    @asIso _ _ _ _ _ hiso ≪≫
    (pushStd f).mapIso (((derivedTensorCanonicalIso X.toRingedSpace).app Z).app
      ((pullStd f).obj ((singleStd S j).obj M))).symm⟩

/-- The coprojections of a derived colimit with the coprojections recorded are compatible with the
transition maps: `cₙ = fₙ ≫ cₙ₊₁`. (The public form is the base's
`CategoryTheory.Pretriangulated.IsHomotopyColimitWith.map_comp_coprojection`, whose file is not
imported here.) -/
private theorem coprojection_eq_of_isHomotopyColimitWith {X : Scheme.{u}} {F : ℕ ⥤ DStd X}
    {K : DStd X} {c : ∀ n, F.obj n ⟶ K} (hK : IsHomotopyColimitWith F K c) (n : ℕ) :
    c n = F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) := by
  obtain ⟨p, q, hT, hc⟩ := hK
  have h := Sigma.ι F.obj n ≫= comp_distTriang_mor_zero₁₂ _ hT
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
    Cofan.mk_ι_app, Preadditive.sub_comp, Category.assoc, comp_zero, sub_eq_zero] at h
  rw [← hc n, ← hc (n + 1), h]

/-- **The construction behind [Stacks, Tag 0DJU], with the pseudo-coherence of `L`.** In
addition to `exists_construction`: `L` is pseudo-coherent, and there is an integer `b` such that
the coprojection `Lₙ ⟶ L` is an isomorphism on `Hⁱ` for every `i ≥ -n + b`. -/
theorem exists_construction_isPseudoCoherent [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (E K : DStd X) (hE : IsRelPerfect f E)
    (hK : IsPseudoCoherentStd K) :
    ∃ (FK : ℕ ⥤ DStd X) (_ : HasCoproduct FK.obj) (c : ∀ n, FK.obj n ⟶ K),
      IsHomotopyColimitWith FK K c ∧ (∀ n, IsPerfectSite (FK.obj n)) ∧
      (∀ (n : ℕ) (i : ℤ), -(n : ℤ) ≤ i → IsIso ((HStd X i).map (c n))) ∧
      (∀ n : ℕ, IsPerfectSite ((pushforwardSheafHomSystem f FK E).obj (op n))) ∧
      ∃ (_ : HasCoproduct (dualSystem (pushforwardSheafHomSystem f FK E)).obj) (L : DStd S)
        (d : ∀ n, (dualSystem (pushforwardSheafHomSystem f FK E)).obj n ⟶ L),
        IsHomotopyColimitWith (dualSystem (pushforwardSheafHomSystem f FK E)) L d ∧
        IsPseudoCoherentStd L ∧
        (∃ b : ℤ, ∀ (n : ℕ) (i : ℤ), -(n : ℤ) + b ≤ i → IsIso ((HStd S i).map (d n))) ∧
        Nonempty ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op K)).obj E) ≅
          ((derivedSheafHom S.sheaf).obj (op L)).obj (unitObj S)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨F, c, hF, hFK, htr⟩ := exists_perfect_system_of_isPseudoCoherent K hK
  have hFtr : ∀ (n : ℕ) (i : ℤ), -(n : ℤ) ≤ i →
      IsIso ((HStd X i).map (F.map (homOfLE (Nat.le_succ n)))) := fun n i hi => by
    have := htr n i hi
    have := htr (n + 1) i (by omega)
    have : IsIso ((HStd X i).map (F.map (homOfLE (Nat.le_succ n))) ≫
        (HStd X i).map (c (n + 1))) := by
      rw [← CategoryTheory.Functor.map_comp, ← coprojection_eq_of_isHomotopyColimitWith hFK n]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((HStd X i).map (c (n + 1)))
  obtain ⟨a, ha⟩ := exists_isGE_derivedTensor_derivedPullback_of_isRelativelyPerfect f E hE
  have hM := isPerfectSite_pushforwardSheafHomSystem f F hF E hE
  let Lsys := dualSystem (pushforwardSheafHomSystem f F E)
  obtain ⟨L, d, hL⟩ := exists_isHomotopyColimitWith_of_hasCoproduct Lsys
  have htrL : ∀ (k : ℕ) (i : ℤ), -(k : ℤ) - a + 1 ≤ i →
      IsIso ((HStd S i).map (Lsys.map (homOfLE (Nat.le_succ k)))) :=
    isIso_homology_dualSystem_map f F hF hFtr E
      (fun Q hQ => isPerfectSite_pushStd f _ (isRelPerfect_sheafHom f Q E hQ hE)) a
      (fun Y m h => ha Y m h)
      (fun Q hQ M hM j => nonempty_pushforward_tensor_single_iso f _
        (isPseudoCoherentStd_of_isRelPerfect (isRelPerfect_sheafHom f Q E hQ hE)) M hM j)
  have hd : ∀ (n : ℕ) (i : ℤ), -(n : ℤ) + (1 - a) ≤ i →
      IsIso ((HStd S i).map (d n)) := fun n i hi =>
    isIso_homology_coprojection hL i n (fun k hk => htrL k i (by omega))
  have hLpc : IsPseudoCoherentStd L :=
    @Stacks.PseudoCoherentHocolim.isPseudoCoherent_of_forall_exists_perfect_isIso S.toRingedSpace
      (stdOXMod _) L (fun m => ⟨Lsys.obj (1 - a - m).toNat, d _,
        isPerfect_ringedSpace_of_isPerfectSite
          (isPerfectSite_dualSystem _ (fun n => hM n.unop) _),
        fun i hi => hd _ i (by omega)⟩)
  exact ⟨F, inferInstance, c, hFK, hF, htr, hM, inferInstance, L, d, hL, hLpc, ⟨1 - a, hd⟩,
    nonempty_iso_pushforward_sheafHom f F E hFK.isHomotopyColimit (fun n => hM n.unop)
      hL.isHomotopyColimit⟩

/-- The base change map is invertible on the terms `R𝓗om(Kₙ, E)` of the system of internal Homs out
of a system of perfect objects into an `S`-perfect object ([Stacks, Tag 0DJT]). -/
theorem isIso_derivedBaseChangeSquare_app_homSystem [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (F : ℕ ⥤ DStd X) (hF : ∀ n, IsPerfectSite (F.obj n))
    (E : DStd X) (hE : IsRelPerfect f E) {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (g : S' ⟶ S) (sq : IsPullback g' f' f g) (n : ℕᵒᵖ) :
    IsIso ((Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)).app
        ((homSystem F E).obj n)) :=
  isIso_derivedBaseChangeSquare_app f ((homSystem F E).obj n)
    (isRelPerfect_sheafHom f (F.obj n.unop) E (hF n.unop) hE) g f' g' sq

/-- **[Stacks, Tag 0DJU].** Let `f : X ⟶ S` be a morphism of schemes and `E, K ∈ D(𝒪_X)`. Assume
`S` is quasi-compact and quasi-separated, `f` is proper, flat and of finite presentation, `E` is
`S`-perfect and `K` is pseudo-coherent. Then there is a pseudo-coherent `L ∈ D(𝒪_S)` with

`Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_S)`,

and the same holds after arbitrary base change: for every cartesian square
`g' ≫ f = f' ≫ g` with `g : S' ⟶ S`,

`Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{S'})`.

The derived categories are read at the standard model `CategoryTheory.HasDerivedCategory.standard`
(`DStd`), at which the derived direct image `pushStd`, the derived pullback `pullStd`, the derived
internal Hom `Stacks.SheafOfModules.derivedSheafHom` and the structure sheaf in degree zero
`unitObj` are taken; "of finite presentation" is `LocallyOfFinitePresentation` together with the
quasi-compactness and quasi-separatedness that properness contains. `L = hocolim Lₙ` for the
duals `Lₙ = (Rf_* R𝓗om(Kₙ, E))^∨` of an approximation `K = hocolim Kₙ` by perfect objects; see
`exists_construction_isPseudoCoherent`. -/
@[stacks 0DJU]
theorem exists_isPseudoCoherent_pushforward_sheafHom_iso [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (E K : DStd X) (hE : IsRelPerfect f E)
    (hK : IsPseudoCoherentStd K) :
    ∃ L : DStd S, IsPseudoCoherentStd L ∧
      Nonempty ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op K)).obj E) ≅
        ((derivedSheafHom S.sheaf).obj (op L)).obj (unitObj S)) ∧
      ∀ {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S), IsPullback g' f' f g →
        Nonempty ((pushStd f').obj (((derivedSheafHom X'.sheaf).obj
            (op ((pullStd g').obj K))).obj ((pullStd g').obj E)) ≅
          ((derivedSheafHom S'.sheaf).obj (op ((pullStd g).obj L))).obj (unitObj S')) := by
  obtain ⟨F, _, _, hFK, hF, -, hM, _, L, _, hL, hLpc, -, hiso⟩ :=
    exists_construction_isPseudoCoherent f E K hE hK
  exact ⟨L, hLpc, hiso, fun g' f' g sq => nonempty_iso_pushforward_sheafHom_pullback f f' g g'
    (comp_toShHom_of_comm sq.w) F hF E hFK.isHomotopyColimit (fun n => hM n.unop)
    (isIso_derivedBaseChangeSquare_app_homSystem f F hF E hE g' f' g sq) hL.isHomotopyColimit⟩

end Assembly

end Stacks.AlgebraicGeometry.RelativeDerivedHomDual

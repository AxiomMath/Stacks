module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.GeneralizationsOfCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces
public import Mathlib.RingTheory.KrullDimension.PID
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing above the dimension on a spectral space

Let `X` be a spectral space of finite Krull dimension `d` and let `F` be an abelian sheaf on `X`.
Then `H^q(X, F) = 0` for every `q > d`. Grothendieck's vanishing theorem for Noetherian spaces
follows.

## Main results

* `Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le`: cohomology of an
  abelian sheaf on a spectral space vanishes in every degree above the Krull dimension of the
  space.
* `Stacks.CohomologyVanishing.subsingleton_sheafH_above_topologicalKrullDim`: the same statement
  with the sheafification and `Ext` data as instance arguments.
* `Stacks.CohomologyVanishing.isCohomologyTransport_of_topologicalKrullDim_eq`: on a spectral
  space of dimension `d ≥ 1`, if cohomology vanishes above the dimension on every spectral space of
  dimension at most `d - 1`, then every abelian sheaf has the transport property
  `Stacks.CohomologyVanishing.IsCohomologyTransport` in degree `d`.
* `Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le`:
  the restriction `H^d(X, F) → H^d(U, F)` to a quasi-compact open is surjective.
* `Stacks.CohomologyVanishing.isStableCompact_specGen_compl_sdiff`: the points specializing into
  the complement of a quasi-compact open `U` and lying in `U` form a quasi-compact subset which is
  stable under generalization.
* `Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`:
  Grothendieck's vanishing theorem for Noetherian spaces.
* `Stacks.CohomologyVanishing.subsingleton_sheafH_primeSpectrum_of_krullDimLE`: cohomology of an
  abelian sheaf on the spectrum of a commutative ring of Krull dimension at most `d` vanishes in
  every degree above `d`.

## References

* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Tag 0AP0](https://stacks.math.columbia.edu/tag/0AP0)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.CohomologyVanishing

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/-- Let `U` be a quasi-compact open of a spectral space `X` and let `E = X ∖ U`. The set of points
which specialize into `E` but do not lie in `E` is quasi-compact and stable under
generalization. -/
theorem isStableCompact_specGen_compl_sdiff (U : Opens X) (hU : IsCompact (U : Set X)) :
    SpectralSubset.IsStableCompact (specGen (U : Set X)ᶜ \ (U : Set X)ᶜ) := by
  have hE : Topology.IsConstructible ((U : Set X)ᶜ) := (hU.isConstructible U.isOpen).compl
  refine ⟨?_, ?_⟩
  · have : SpectralSpace ↥(specGen (U : Set X)ᶜ \ (U : Set X)ᶜ) :=
      isSpectral_specGen_diff_constructible hE
    exact isCompact_iff_compactSpace.mpr inferInstance
  · intro x y hxy hx
    refine ⟨stableUnderGeneralization_specGen _ hxy hx.1, ?_⟩
    have hxU : x ∈ U := by simpa using hx.2
    simpa using hxy.mem_open U.isOpen hxU

/-- A space whose Krull dimension is not `⊥` and is smaller than a natural number has Krull
dimension a natural number. -/
private theorem exists_nat_eq_topologicalKrullDim_of_lt {Y : Type u} [TopologicalSpace Y] {n : ℕ}
    (hbot : topologicalKrullDim Y ≠ ⊥) (h : topologicalKrullDim Y < (n : WithBot ℕ∞)) :
    ∃ e : ℕ, topologicalKrullDim Y = (e : WithBot ℕ∞) := by
  generalize topologicalKrullDim Y = a at *
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (not_lt_of_ge (by exact_mod_cast le_top))
    | coe e => exact ⟨e, rfl⟩

/-- A space whose Krull dimension is smaller than a natural number `d` has Krull dimension at
most `d - 1`. -/
private theorem topologicalKrullDim_le_pred {Y : Type u} [TopologicalSpace Y] {d : ℕ}
    (h : topologicalKrullDim Y < (d : WithBot ℕ∞)) :
    topologicalKrullDim Y ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  by_cases hbot : topologicalKrullDim Y = ⊥
  · rw [hbot]; exact bot_le
  obtain ⟨e, he⟩ := exists_nat_eq_topologicalKrullDim_of_lt hbot h
  rw [he] at h ⊢
  exact_mod_cast Nat.le_pred_of_lt (by exact_mod_cast h)

/-- A nonempty space of Krull dimension at most a natural number `d` has Krull dimension a
natural number `e ≤ d`. -/
private theorem exists_nat_eq_topologicalKrullDim {Y : Type u} [TopologicalSpace Y] [Nonempty Y]
    {d : ℕ} (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, topologicalKrullDim Y = (e : WithBot ℕ∞) ∧ e ≤ d := by
  have hbot : topologicalKrullDim Y ≠ ⊥ := fun h =>
    not_isEmpty_of_nonempty Y ((topologicalKrullDim_eq_bot_iff_isEmpty Y).mp h)
  obtain ⟨e, he⟩ := exists_nat_eq_topologicalKrullDim_of_lt (n := d + 1) hbot
    (hdim.trans_lt (by exact_mod_cast Nat.lt_succ_self d))
  rw [he] at hdim
  exact ⟨e, he, by exact_mod_cast hdim⟩

/-- An abelian sheaf on an empty space has vanishing cohomology in every positive degree. -/
theorem subsingleton_sheafH_of_isEmpty {Y : Type u} [TopologicalSpace Y] [IsEmpty Y]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u, u, u, u} G q) :=
  cohomology_subsingleton_of_isProfiniteStacks
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected Y).2
      ⟨inferInstance, inferInstance, inferInstance⟩) G q hq

/-- Let `K` be a quasi-compact subset of a spectral space `X` which is stable under
generalization, let `F` be an abelian sheaf on `X` and suppose the degree-`d` cohomology of `F|_K`
vanishes. Then every degree-`d` class over an open neighbourhood `U` of `K` dies on a smaller open
neighbourhood of `K`. -/
private theorem exists_openNhd_map_eq_zero
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (K : Set X)
    (hK : SpectralSubset.IsStableCompact K) (d : ℕ)
    (hvanish : Subsingleton
      ((((Stacks.Topology.restrictionFunctor (TopCat.of X) K).obj F).cohomologyPresheaf d).obj
        (op (⊤ : Opens (TopCat.of K)))))
    (U : Opens X) (hKU : K ⊆ (U : Set X))
    (ξ : (F.cohomologyPresheaf d).obj (op U)) :
    ∃ (O : Opens X) (_ : K ⊆ (O : Set X)) (hOU : O ≤ U),
      (F.cohomologyPresheaf d).map (homOfLE hOU).op ξ = 0 := by
  have := Stacks.Topology.isIso_cohomologyOfClosedMap_of_isStableCompact
    (X := TopCat.of X) K hK F d
  have := hvanish
  have hzero : colimit.ι (Stacks.Topology.openNeighborhoodCohomology (X := TopCat.of X) K F d)
        (op ⟨U, hKU⟩) ξ =
      colimit.ι (Stacks.Topology.openNeighborhoodCohomology (X := TopCat.of X) K F d)
        (op ⟨U, hKU⟩) 0 :=
    (ConcreteCategory.bijective_of_isIso
      (Stacks.Topology.cohomologyOfClosedMap (X := TopCat.of X) K F d)).1 (Subsingleton.elim _ _)
  obtain ⟨W, f, g, hfg⟩ :=
    Stacks.Topology.exists_map_eq_of_colimit_ι_eq (X := TopCat.of X) K F d
      (U := op ⟨U, hKU⟩) (V := op ⟨U, hKU⟩) ξ 0 hzero
  have hfhom : W.unop.obj ⟶ U :=
    (Stacks.Topology.openNhdsSetInclusion (X := TopCat.of X) K).map f.unop
  refine ⟨W.unop.obj, W.unop.property, leOfHom hfhom, ?_⟩
  rw [show homOfLE (leOfHom hfhom) =
    (Stacks.Topology.openNhdsSetInclusion (X := TopCat.of X) K).map f.unop from
      Subsingleton.elim _ _]
  exact hfg.trans (map_zero _)

/-- Let `X` be a spectral space of Krull dimension `d ≥ 1` and let `F` be an abelian sheaf on
`X`. If cohomology vanishes above the dimension on every spectral space of dimension at most
`d - 1`, then `F` has the transport property of `Stacks.CohomologyVanishing.IsCohomologyTransport`
in degree `d`: every degree-`d` class over a quasi-compact open `U` dies on `U ⊓ V` for some
quasi-compact open `V ⊇ X ∖ U`. -/
theorem isCohomologyTransport_of_topologicalKrullDim_eq
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d : ℕ) (hd : 0 < d)
    (hdim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hlow : ∀ (Y : Type u) [TopologicalSpace Y] [SpectralSpace Y]
      (_hs : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
      (_he : HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))
      (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (q : ℕ),
      topologicalKrullDim Y ≤ ((d - 1 : ℕ) : WithBot ℕ∞) → (d - 1 : ℕ) < q →
        Subsingleton (Sheaf.H.{u, u, u, u} G q)) :
    IsCohomologyTransport F d := by
  intro U hU ξ
  set K : Set X := specGen (U : Set X)ᶜ \ (U : Set X)ᶜ
  have hE : Topology.IsConstructible ((U : Set X)ᶜ) := (hU.isConstructible U.isOpen).compl
  have hK : SpectralSubset.IsStableCompact K := isStableCompact_specGen_compl_sdiff U hU
  have hKU : K ⊆ (U : Set X) := fun _ hx => by simpa using hx.2
  have hKspec : SpectralSpace ↥K := isSpectral_specGen_diff_constructible hE
  have hKdim : topologicalKrullDim ↥K ≤ ((d - 1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_le_pred
      (topologicalKrullDim_specGen_sdiff_lt d hdim ((U : Set X)ᶜ) hE)
  let heK : HasExt.{u}
      (Sheaf (Opens.grothendieckTopology (TopCat.of K)) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  have hvanish : Subsingleton
      ((((Stacks.Topology.restrictionFunctor (TopCat.of X) K).obj F).cohomologyPresheaf d).obj
        (op (⊤ : Opens (TopCat.of K)))) :=
    (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
      ((Stacks.Topology.restrictionFunctor (TopCat.of X) K).obj F) d).1
      (hlow ↥K inferInstance heK _ d hKdim (by omega))
  obtain ⟨W, hKW, hWU, hξW⟩ := exists_openNhd_map_eq_zero F K hK d hvanish U hKU ξ
  obtain ⟨O, hO⟩ := Stacks.Topology.StableCompact.exists_subset (X := TopCat.of X) K hK
    W.isOpen hKW
  obtain ⟨V, hVc, hsup, hinf⟩ := exists_isCompact_sup_eq_top_inf_le U ⟨(O : Set X), O.2.1⟩ hU
    O.2.2.1 O.2.2.2
  refine ⟨V, hVc, ?_, ?_⟩
  · intro x hx
    exact (show x ∈ U ⊔ V by rw [hsup]; trivial).resolve_left hx
  · have hle : U ⊓ V ≤ W := fun x hx => hO (hinf hx)
    have hres := congrArg (fun a => (F.cohomologyPresheaf d).map (homOfLE hle).op a) hξW
    simp only [map_zero] at hres
    rw [← hres, ← Functor.map_comp_apply, ← op_comp]
    exact congrArg (fun a : (U ⊓ V : Opens X) ⟶ U => (F.cohomologyPresheaf d).map a.op ξ)
      (Subsingleton.elim _ _)

/-- Let `Y` be a spectral space of Krull dimension at most `d` and let `G` be an abelian sheaf on
`Y`. Then `H^q(Y, G) = 0` for every `q > d`. -/
@[stacks 0A3G "clause (1): on a spectral space, sheaf cohomology vanishes above the \
  dimension"]
theorem subsingleton_sheafH_of_topologicalKrullDim_le :
    ∀ (d : ℕ) (Y : Type u) [TopologicalSpace Y] [SpectralSpace Y]
      (_hs : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
      (_he : HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))
      (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (q : ℕ),
      topologicalKrullDim Y ≤ (d : WithBot ℕ∞) → d < q →
        Subsingleton (Sheaf.H.{u, u, u, u} G q) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro Y _ _ hs he G q hdim hq
    have := hs
    have := he
    by_cases hempty : IsEmpty Y
    · have := hempty
      exact subsingleton_sheafH_of_isEmpty G q (by omega)
    have hne : Nonempty Y := not_isEmpty_iff.mp hempty
    obtain ⟨e, hdimE, hed⟩ := exists_nat_eq_topologicalKrullDim hdim
    rcases Nat.eq_zero_or_pos e with he0 | hepos
    · subst he0
      exact cohomology_subsingleton_of_topologicalKrullDim_eq_zero G q
        (by exact_mod_cast hdimE) (by omega)
    · have hlow : ∀ (Z : Type u) [TopologicalSpace Z] [SpectralSpace Z]
          (_hs : HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
          (_he : HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}))
          (H : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (r : ℕ),
          topologicalKrullDim Z ≤ ((e - 1 : ℕ) : WithBot ℕ∞) → (e - 1 : ℕ) < r →
            Subsingleton (Sheaf.H.{u, u, u, u} H r) := by
        intro Z _ _ hsZ heZ H r hZ hr
        exact ih (e - 1) (by omega) Z hsZ heZ H r hZ hr
      exact subsingleton_sheafH_of_isCohomologyTransport G e
        (isCohomologyTransport_of_topologicalKrullDim_eq G e hepos hdimE hlow) q (by omega)

/-- Let `Y` be a spectral space of Krull dimension at most `d` and let `G` be an abelian sheaf on
`Y`. Then `H^q(Y, G) = 0` for every `q > d`. -/
@[stacks 0A3G "clause (1): on a spectral space of Krull dimension at most d, sheaf cohomology \
  vanishes in every degree above d.  The same statement as the induction carrier \
  subsingleton_sheafH_of_topologicalKrullDim_le, whose explicit HasSheafify and HasExt arguments \
  are instance arguments here"]
theorem subsingleton_sheafH_above_topologicalKrullDim {Y : Type u} [TopologicalSpace Y]
    [SpectralSpace Y]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (d q : ℕ)
    (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    Subsingleton (Sheaf.H.{u, u, u, u} G q) :=
  subsingleton_sheafH_of_topologicalKrullDim_le d Y inferInstance inferInstance G q hdim hq

omit [SpectralSpace X] in
/-- Sheaf cohomology over the empty open vanishes in every degree. -/
private theorem subsingleton_sheafH'_bot
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (F.H' n (⊥ : Opens X)) := by
  let J := Opens.grothendieckTopology X
  let P := Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) (⊥ : Opens X)
  have hbot : (⊥ : Sieve (⊥ : Opens X)) ∈ J (⊥ : Opens X) :=
    (Opens.mem_grothendieckTopology (T := X) (U := ⊥) (S := ⊥)).2 (by simp)
  have hsections (G : Sheaf J AddCommGrpCat.{u}) :
      Subsingleton (G.obj.obj (op (⊥ : Opens X))) :=
    AddCommGrpCat.subsingleton_of_isZero
      (Sheaf.isTerminalOfBotCover G (⊥ : Opens X) hbot).isZero
  let rep (G : Sheaf J AddCommGrpCat.{u}) :
      (P ⟶ G) ≃ G.obj.obj (op (⊥ : Opens X)) :=
    (sheafificationAdjunction J AddCommGrpCat).homEquiv _ _ |>.trans
      (Stacks.Cohomology.Locality.repEquiv (⊥ : Opens X) G.obj)
  have hPinit : IsInitial P := by
    let : ∀ G : Sheaf J AddCommGrpCat.{u}, Unique (P ⟶ G) := fun G =>
      { default := (rep G).symm 0
        uniq := fun f => (rep G).injective ((hsections G).elim _ _) }
    exact IsInitial.ofUnique P
  let hP : IsZero P := hPinit.isZero
  change Subsingleton (Abelian.Ext.{u} P F n)
  cases n with
  | zero =>
    let : Subsingleton (P ⟶ F) := ⟨fun f g => hP.eq_of_src f g⟩
    exact (Equiv.subsingleton_congr Abelian.Ext.addEquiv₀.toEquiv).2 inferInstance
  | succ n =>
    let : Projective P := hP.projective
    exact subsingleton_of_forall_eq 0 (fun ξ => Abelian.Ext.eq_zero_of_projective ξ)

/-- On a spectral space of Krull dimension zero every abelian sheaf has the property of
`Stacks.CohomologyVanishing.IsCohomologyTransport` in degree `0`. -/
private theorem isCohomologyTransport_of_topologicalKrullDim_eq_zero
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hdim : topologicalKrullDim X = ((0 : ℕ) : WithBot ℕ∞)) :
    IsCohomologyTransport F 0 := by
  obtain ⟨-, hT2, -⟩ := (isProfiniteStacks_iff_compact_t2_totallyDisconnected X).1
    (isProfiniteStacks_of_topologicalKrullDim_eq_zero (by exact_mod_cast hdim))
  have := hT2
  intro U hU ξ
  have hUclosed : IsClosed (U : Set X) := hU.isClosed
  refine ⟨⟨(U : Set X)ᶜ, hUclosed.isOpen_compl⟩,
    (isClosed_compl_iff.2 U.isOpen).isCompact, subset_rfl, ?_⟩
  have hbot : U ⊓ (⟨(U : Set X)ᶜ, hUclosed.isOpen_compl⟩ : Opens X) = ⊥ := by
    ext x; simp
  have hsub : Subsingleton ((F.cohomologyPresheaf 0).obj
      (op (U ⊓ (⟨(U : Set X)ᶜ, hUclosed.isOpen_compl⟩ : Opens X)))) := by
    rw [hbot]
    exact subsingleton_sheafH'_bot F 0
  exact @Subsingleton.elim _ hsub _ _

/-- Let `X` be a spectral space of Krull dimension at most `d` and let `F` be an abelian sheaf on
`X`. Then the restriction `H^d(X, F) → H^d(U, F)` is surjective for every quasi-compact open
`U ⊆ X`. -/
@[stacks 0A3G "clause (2): surjectivity of the restriction H^d(X,F) → H^d(U,F) for U \
  quasi-compact open"]
theorem surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    Function.Surjective
      ((F.cohomologyPresheaf d).map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  by_cases hempty : IsEmpty X
  · have hUbot : U = ⊥ := by ext x; exact hempty.elim x
    have hsub : Subsingleton ((F.cohomologyPresheaf d).obj (op U)) := by
      rw [hUbot]
      exact subsingleton_sheafH'_bot F d
    exact fun ξ => ⟨0, @Subsingleton.elim _ hsub _ _⟩
  · have hne : Nonempty X := not_isEmpty_iff.mp hempty
    obtain ⟨e, hdimE, hed⟩ := exists_nat_eq_topologicalKrullDim hdim
    have htr : IsCohomologyTransport F e := by
      rcases Nat.eq_zero_or_pos e with he0 | hepos
      · subst he0
        exact isCohomologyTransport_of_topologicalKrullDim_eq_zero F hdimE
      · refine isCohomologyTransport_of_topologicalKrullDim_eq F e hepos hdimE ?_
        intro Y _ _ hsY heY G q hY hq
        exact subsingleton_sheafH_of_topologicalKrullDim_le (e - 1) Y hsY heY G q hY hq
    rcases eq_or_lt_of_le hed with rfl | hlt
    · exact surjective_cohomologyPresheaf_map_top_of_isCohomologyTransport F e htr U hU
    · have hsub := cohomology_subsingleton_of_isCohomologyTransport F e htr d hlt U hU
      exact fun ξ => ⟨0, @Subsingleton.elim _ hsub _ _⟩

/-- Grothendieck's vanishing theorem. Let `X` be a Noetherian topological space of topological
Krull dimension at most `d` and let `F` be an abelian sheaf on `X`. Then `H^p(X, F) = 0` for every
`p > d`. -/
@[stacks 02UZ]
theorem subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    {d p : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hp : d < p)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Subsingleton (Sheaf.H.{u, u, u, u} F p) := by
  have hspec : SpectralSpace (Soberification X) := spectralSpace_soberification
  let hsheafify : HasSheafify (Opens.grothendieckTopology (Soberification X))
      AddCommGrpCat.{u} :=
    hasSheafify_of_opensOrderIso (soberificationOpensOrderIso (X := X))
      (isDenseSubsite_of_opensOrderIso (soberificationOpensOrderIso (X := X)).symm)
  have hext : HasExt.{u}
      (Sheaf (Opens.grothendieckTopology (Soberification X)) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  exact subsingleton_sheafCohomology_of_noetherianSpace
    (fun Y _ _ hsY heY G e q hdY hq =>
      subsingleton_sheafH_of_topologicalKrullDim_le e Y hsY heY G q hdY hq)
    hdim hp F

/-- On the spectrum of a commutative ring of Krull dimension at most `d`, every abelian sheaf has
vanishing cohomology in every degree above `d`. -/
theorem subsingleton_sheafH_primeSpectrum_of_krullDimLE (R : Type u) [CommRing R] (d : ℕ)
    [Ring.KrullDimLE d R]
    (F : Sheaf (Opens.grothendieckTopology (PrimeSpectrum R)) AddCommGrpCat.{u}) (q : ℕ)
    (hq : d < q) : Subsingleton (Sheaf.H.{u, u, u, u} F q) := by
  have hdim : topologicalKrullDim (PrimeSpectrum R) ≤ ((d : ℕ) : WithBot ℕ∞) := by
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact_mod_cast Ring.krullDimLE_iff.mp ‹_›
  exact subsingleton_sheafH_of_topologicalKrullDim_le d (PrimeSpectrum R) inferInstance
    (hasExt_of_enoughInjectives _) F q hdim hq

/-- The spectrum of `ℤ` has topological Krull dimension exactly `1`. -/
theorem topologicalKrullDim_primeSpectrum_int :
    topologicalKrullDim (PrimeSpectrum ℤ) = 1 := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

/-- `Spec ℤ` is not discrete. -/
theorem not_discreteTopology_primeSpectrum_int :
    ¬ DiscreteTopology (PrimeSpectrum ℤ) := fun _ ↦ by
  simpa [topologicalKrullDim_eq_zero_of_discreteTopology_nonempty] using
    topologicalKrullDim_primeSpectrum_int

end Stacks.CohomologyVanishing

end

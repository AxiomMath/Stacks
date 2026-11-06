module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.ProblemStep
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono

/-!
# Absolute Noetherian approximation of algebraic spaces

This file proves Stacks 07SU: a quasi-compact and quasi-separated algebraic space over
`Spec ℤ` is the limit of a directed inverse system of algebraic spaces with affine transition
morphisms, each quasi-separated and of finite type over `Spec ℤ`.

The proof follows the source. By Stacks 07ST the space has a finite filtration
`∅ = U_n ⊆ U_{n-1} ⊆ … ⊆ U_0 = X` by open subspaces, with surjective étale morphisms
`f_p : V_p ⟶ U_p` from quasi-compact separated schemes which are isomorphisms over the reduced
strata `U_p ∖ U_{p+1}`. Descending induction on `p`, starting from the empty space and running
the problem step of the proof
(`AlgebraicGeometry.Space.QuotientApproximation.problemStep`) at each stratum, presents every
`U_p` as the limit of a system of étale quotients `V_i / R_i` of finite type over `Spec ℤ`
(`AlgebraicGeometry.Space.QuotientApproximation`), and such a presentation is a Noetherian
approximation.

## Main results

* `AlgebraicGeometry.Space.QuotientApproximation.ofRepresentable`: an object of the site which is
  quasi-compact and locally of finite type over `Spec ℤ` presents itself.
* `AlgebraicGeometry.Space.nonempty_quotientApproximation`: every quasi-compact quasi-separated
  algebraic space over `Spec ℤ` is presented by a system of étale quotients of finite type.

Stacks 07SU itself is `AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`
in `StacksFrontier/AlgebraicGeometry/Spaces/AbsoluteNoetherianApproximation/Main.lean`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]

namespace QuotientApproximation

/-- The identity cone over a constant diagram on the one-point index category is a limit. -/
noncomputable def isLimitConstPUnit {C : Type*} [Category C] (Y : C) :
    IsLimit (Cone.mk Y (𝟙 ((Functor.const PUnit.{u + 1}ᵒᵖ).obj Y))) where
  lift s := s.π.app (op PUnit.unit)
  fac s j := by
    obtain rfl : j = op PUnit.unit := rfl
    simp
  uniq s m h := by simpa using h (op PUnit.unit)

/-- **An object of the site quasi-compact and locally of finite type over `Spec ℤ` presents
itself**, by the constant system of the trivial relation on it. -/
noncomputable def ofRepresentable (Y : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y)]
    [LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y))] :
    QuotientApproximation hZ (yoneda.obj Y) :=
  have := isMultiplicative_presheaf_surjective B (⊤_ Scheme.{u}) hZ
  have := isMultiplicative_presheaf_etale B (⊤_ Scheme.{u}) hZ
  { I := PUnit.{u + 1}
    E :=
      { obj := (Functor.const _).obj Y
        rel := (Functor.const _).obj Y
        s := 𝟙 _
        t := 𝟙 _
        isEtaleEquivalenceRelation := fun _ => isEtaleEquivalenceRelation_id B _ hZ Y
        isPullback_s := fun _ => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, NatTrans.id_app,
            CategoryTheory.Functor.map_id]
          exact IsPullback.of_horiz_isIso ⟨rfl⟩ }
    hobj := fun _ => by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, CategoryTheory.Functor.map_id]
      infer_instance
    hcpt := fun _ => ‹CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y)›
    hlft := fun _ => ‹LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y))›
    hrel := fun _ => ‹CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y)›
    cV := Cone.mk Y (𝟙 _)
    hV := isLimitConstPUnit _
    cR := Cone.mk Y (𝟙 _)
    hR := isLimitConstPUnit _
    sL := 𝟙 _
    tL := 𝟙 _
    hs := fun _ => by simp
    ht := fun _ => by simp
    f := 𝟙 _
    hf := by
      simp only [CategoryTheory.Functor.map_id]
      exact IsPullback.of_horiz_isIso ⟨rfl⟩
    hsurj := MorphismProperty.id_mem _ _
    hetale := MorphismProperty.id_mem _ _ }

omit [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)] in
/-- **The empty open subspace is presented** by the constant system on the empty scheme: the
sheafified bottom subfunctor of an algebraic space is represented by the empty object of the
site. -/
theorem nonempty_sheafify_bot {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) :
    Nonempty (QuotientApproximation hZ
      ((⊥ : Subfunctor X).sheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)).toFunctor) := by
  let J := BigFppfOver.topology B (⊤_ Scheme.{u}) hZ
  let E0 := BigFppfOver.initialObj B (⊤_ Scheme.{u}) hZ
  have hE : B.Contains (∅ : Scheme.{u}) :=
    lt_of_le_of_lt AlgebraicGeometry.Scheme.size_empty_le_aleph0 B.aleph0_lt_cutoff
  have hbot : (⊥ : Sieve E0) ∈ BigFppfOver.topology B (⊤_ Scheme.{u}) hZ E0 := by
    have hb : (⊥ : Sieve E0.left) ∈ B.topology E0.left :=
      AlgebraicGeometry.BigFppfSite.bot_mem_topology_obj_contains_empty B hE
    rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff]
    simpa using hb
  let bot : Subfunctor X := ⊥
  let I := bot.sheafify J
  have hX' : Presieve.IsSheaf J X := (isSheaf_iff_isSheaf_of_type J X).mp hX.isSheaf
  have hI : Presieve.IsSheaf J I.toFunctor := bot.sheafify_isSheaf hX'
  have hEY : Presheaf.IsSheaf J (yoneda.obj E0) :=
    (isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ E0).isSheaf
  have hE' : Presieve.IsSheaf J (yoneda.obj E0) := (isSheaf_iff_isSheaf_of_type J _).mp hEY
  let eI : Sheaf J (Type u) := ⟨I.toFunctor, (isSheaf_iff_isSheaf_of_type J _).mpr hI⟩
  let eE : Sheaf J (Type u) := ⟨yoneda.obj E0, hEY⟩
  have hIunique (a b : I.toFunctor ⟶ I.toFunctor) : a = b := by
    apply bot.to_sheafify_lift_unique hI
    ext T x
    exact (Set.notMem_empty _ x.property).elim
  have hEterm : IsTerminal (eE.1.obj (op E0)) := Sheaf.isTerminalOfBotCover eE _ hbot
  have hEunique (a b : eE.1 ⟶ eE.1) : a = b := by
    let : Unique (eE.1.obj (op E0)) := Types.isTerminalEquivUnique _ hEterm
    exact yonedaEquiv.injective (Subsingleton.elim _ _)
  let f0 : bot.toFunctor ⟶ eE.1 :=
    { app T := ↾fun x => (Set.notMem_empty _ x.property).elim
      naturality := by
        intro T T' f
        ext x
        exact (Set.notMem_empty _ x.property).elim }
  let f : eI.1 ⟶ eE.1 := bot.sheafifyLift f0 hE'
  let x : eI.1.obj (op E0) := by
    let : Unique (eI.1.obj (op E0)) :=
      Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover eI _ hbot)
    exact default
  let g : eE.1 ⟶ eI.1 := yonedaEquiv.symm x
  have : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj E0) :=
    inferInstanceAs (CompactSpace (∅ : Scheme.{u}))
  have : LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj E0)) :=
    inferInstanceAs (LocallyOfFiniteType (terminal.from (∅ : Scheme.{u})))
  exact ⟨(ofRepresentable E0).ofIso ⟨g, f, hEunique _ _, hIunique _ _⟩⟩

end QuotientApproximation

/-- For subfunctors `H ≤ G` of a presheaf, the inverse image of `H` under the inclusion of `G`
is `H`. -/
noncomputable def subfunctorPreimageIsoOfLE {C : Type*} [Category C] {F : C ⥤ Type u}
    {G H : Subfunctor F} (h : H ≤ G) : (H.preimage G.ι).toFunctor ≅ H.toFunctor :=
  NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, h _ x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; rfl)

/-- **Every quasi-compact quasi-separated algebraic space over `Spec ℤ` is the limit of a system
of étale quotients of finite type over `Spec ℤ`** (the proof of Stacks 07SU): descending
induction along the stratification of Stacks 07ST, from the empty open subspace, by the problem
step `AlgebraicGeometry.Space.QuotientApproximation.problemStep`. -/
theorem nonempty_quotientApproximation {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    Nonempty (QuotientApproximation hZ X) := by
  obtain ⟨n, U, hn, hU0, hUn, hUopen, hUmono, T, V, f, hdata⟩ :=
    exists_finiteFiltration_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ X hX hqc hqs
  have key : ∀ m, m ≤ n → Nonempty (QuotientApproximation hZ (U (n - m)).toFunctor) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, hUn]
      exact QuotientApproximation.nonempty_sheafify_bot hX
    | succ m ih =>
      intro hm
      have hp1 : n - (m + 1) + 1 = n - m := by omega
      have hpn : n - (m + 1) < n := by omega
      obtain ⟨AU⟩ := ih (Nat.le_of_succ_le hm)
      rw [← hp1] at AU
      set p := n - (m + 1)
      obtain ⟨_, hTpts, _, hVc, hVsep, hfsurj, hfet, hiso⟩ := hdata ⟨p, hpn⟩
      have hXp : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (U p).toFunctor := (hUopen p hpn.le).1
      have hXpqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (U p).toFunctor :=
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ hXp hqs
          (isQuasiSeparated_of_mono B (⊤_ Scheme.{u}) hZ (U p).ι inferInstance)
      let U' : Subfunctor (U p).toFunctor := (U (p + 1)).preimage (U p).ι
      have hU' : IsOpenSubspace B (⊤_ Scheme.{u}) hZ U' :=
        isOpenSubspace_preimage B (⊤_ Scheme.{u}) hZ (U p).ι (U (p + 1)) hX hXp
          (hUopen (p + 1) (by omega))
      let AU' := AU.ofIso (subfunctorPreimageIsoOfLE (hUmono p hpn)).symm
      have hinj := pointsMap_injective_of_mono B (⊤_ Scheme.{u}) hZ (U p).ι
      have hU'pts : Set.range (pointsMap B (⊤_ Scheme.{u}) hZ U'.toFunctor U'.ι) =
          pointsMap B (⊤_ Scheme.{u}) hZ (U p).toFunctor (U p).ι ⁻¹'
            Set.range (pointsMap B (⊤_ Scheme.{u}) hZ (U (p + 1)).toFunctor (U (p + 1)).ι) := by
        have h := preimage_image_pointsMap_of_isPullback B (⊤_ Scheme.{u}) hZ
          (Subfunctor.isPullback_preimage (U p).ι (U (p + 1))) Set.univ
        simpa [Set.image_univ] using h.symm
      have hUZ : Set.range (pointsMap B (⊤_ Scheme.{u}) hZ (T ⟨p, hpn⟩).toFunctor
          (T ⟨p, hpn⟩).ι) =
          (Set.range (pointsMap B (⊤_ Scheme.{u}) hZ U'.toFunctor U'.ι))ᶜ := by
        have himg : (pointsMap B (⊤_ Scheme.{u}) hZ (U p).toFunctor (U p).ι) ''
            Set.range (pointsMap B (⊤_ Scheme.{u}) hZ (T ⟨p, hpn⟩).toFunctor
              (T ⟨p, hpn⟩).ι) =
            Set.range (pointsMap B (⊤_ Scheme.{u}) hZ (T ⟨p, hpn⟩).toFunctor
              ((T ⟨p, hpn⟩).ι ≫ (U p).ι)) := by
          rw [← Set.range_comp]
          exact congrArg _ (funext fun z => (pointsMap_comp_apply B (⊤_ Scheme.{u}) hZ _ _ z).symm)
        rw [hU'pts, ← hinj.preimage_image (Set.range _), himg, hTpts]
        ext y
        simp
      exact QuotientApproximation.problemStep hXp hXpqs U' hU' AU' (T ⟨p, hpn⟩) hUZ (V ⟨p, hpn⟩)
        (f ⟨p, hpn⟩) hfsurj hfet hiso
  obtain ⟨A⟩ := key n le_rfl
  rw [Nat.sub_self, hU0] at A
  exact ⟨A.ofIso (asIso (⊤ : Subfunctor X).ι)⟩

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpace

/-!
# Sections of an algebraic space over a complete local ring, from its truncations

Let `R` be a Noetherian complete local ring and `X` an algebraic space over a scheme `S`.
**Stacks 0AQH** says that a morphism `Spec R ⟶ X` over `S` is the same thing as a morphism
from the formal spectrum `Spf R`. This file restates that bijection without formal spectra:
a section of `X` over `Spec R` is the same thing as a compatible family of sections over the
spectra of the quotients `R ⧸ J n`, for any decreasing sequence of ideals `J n` cofinal with
the powers of the maximal ideal.

That is the form in which the theorem is consumed by deformation theory: the levels of a
formal object of a category fibred in groupoids live over the infinitesimal thickenings
`Spec (R ⧸ 𝔪 ^ (n + 1))` and nothing else, and for a finite extension `R ⊆ R'` of complete
local rings the thickenings of `R` pull back to the quotients `R' ⧸ 𝔪 ^ (n + 1) R'`, which are
cofinal with, but not equal to, the powers of the maximal ideal of `R'`.

## Main results

* `AlgebraicGeometry.FormalSpace.existsUnique_section_of_compatible_truncations`: a compatible
  family of sections over the truncations comes from a unique section over `Spec R`. The
  objects of the site carrying the truncations are arbitrary, identified with the spectra of the
  quotients by given isomorphisms of schemes.

## Implementation notes

Existence is the surjectivity half of Stacks 0AQH,
`AlgebraicGeometry.FormalSpace.bijective_map_into_algebraicSpace`, for the `𝔪`-adic topology:
its weak ideals of definition are the ideals between a power of `𝔪` and `𝔪`, so the given
sequence is cofinal among them and the family of sections, read through the Yoneda lemma for
sheaves, is a cocone over a final subdiagram of the diagram whose colimit is the formal
spectrum. Uniqueness is `AlgebraicGeometry.FormalSpace.eq_of_forall_quotientPow_factorization`,
which needs a factorization of every truncation `Spec (R ⧸ 𝔪 ^ k)` through some `Spec (R ⧸ J n)`.

## References

* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Adic

variable {R : Type u} [CommRing R] [IsLocalRing R]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- For the `𝔪`-adic topology of a local ring, an ideal lying between a power of `𝔪` and `𝔪`
is a weak ideal of definition. -/
private lemma isWeakIdealOfDefinition_of_between_maximalIdeal_powers (I : Ideal R)
    (h₁ : ∃ k : ℕ, maximalIdeal R ^ k ≤ I) (h₂ : I ≤ maximalIdeal R) :
    @TopologicalRing.IsWeakIdealOfDefinition R _ (maximalIdeal R).adicTopology I := by
  let : TopologicalSpace R := (maximalIdeal R).adicTopology
  let : NonarchimedeanRing R := (maximalIdeal R).nonarchimedean
  obtain ⟨k, hk⟩ := h₁
  refine ⟨?_, ?_⟩
  · exact I.toAddSubgroup.isOpen_of_mem_nhds
      ((maximalIdeal R).hasBasis_nhds_zero_adic.mem_iff.2 ⟨k, trivial, hk⟩)
  · intro x hx
    change Filter.Tendsto (fun j : ℕ => x ^ j) Filter.atTop (nhds 0)
    rw [Filter.atTop_basis.tendsto_iff (maximalIdeal R).hasBasis_nhds_zero_adic]
    intro j _
    exact ⟨j, trivial, fun l hl => Ideal.pow_le_pow_right hl (Ideal.pow_mem_pow (h₂ hx) l)⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- For the `𝔪`-adic topology of a local ring, a weak ideal of definition contains a power
of `𝔪`. -/
private lemma exists_maximalIdeal_pow_le_of_isWeakIdealOfDefinition (I : Ideal R)
    (hI : @TopologicalRing.IsWeakIdealOfDefinition R _ (maximalIdeal R).adicTopology I) :
    ∃ k : ℕ, maximalIdeal R ^ k ≤ I := by
  let : TopologicalSpace R := (maximalIdeal R).adicTopology
  exact ((maximalIdeal R).hasBasis_nhds_zero_adic.mem_iff.1 (hI.1.mem_nhds I.zero_mem)).imp
    fun _ h => h.2

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The quotient system of the `𝔪`-adic topology of a local ring whose spectrum lies in the
site: every quotient is a closed subscheme of `Spec R`, hence in the site, and lies over `S`
through `Spec R`. -/
private def maximalIdealAdicQuotientSystem (hRS : B.Contains (Spec (.of R)))
    (p : Spec (.of R) ⟶ S) :
    @QuotientSystem B S hS R _ (maximalIdeal R).adicTopology := by
  letI : TopologicalSpace R := (maximalIdeal R).adicTopology
  refine ⟨fun J => ?_, fun J => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p,
    fun J L h => ?_⟩
  · have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk J.1))
      Ideal.Quotient.mk_surjective
    exact Scheme.size_lt_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))) hRS
  · rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

end Adic

section Colimit

variable {R : Type u} [CommRing R] [TopologicalSpace R]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A family of maps out of the represented stages of a decreasing sequence of weak ideals of
definition, cofinal among all of them and compatible with the transition maps, factors through
the formal spectrum. -/
private lemma exists_formalSpectrum_desc_of_decreasing_cofinal (D : QuotientSystem B S hS R)
    (I : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (hI : ∀ n, I (n + 1) ≤ I n)
    (hcof : ∀ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, (I n).1 ≤ L.1)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (z : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (I n)) ⟶ Y)
    (hz : ∀ n, (formalSpectrumDiagram D).map (homOfLE (hI n)) ≫ z (n + 1) = z n) :
    ∃ q : formalSpectrum D ⟶ Y,
      ∀ n, formalSpectrumInclusion D (OrderDual.toDual (I n)) ≫ q = z n := by
  have hmono : Monotone (fun n => OrderDual.toDual (I n)) :=
    monotone_nat_of_le_succ fun n => OrderDual.toDual_le_toDual.2 (hI n)
  let P := hmono.functor
  have : P.Final :=
    (Monotone.final_functor_iff hmono).2 fun L => (hcof (OrderDual.ofDual L)).imp fun _ h => h
  let G := formalSpectrumDiagram D
  let H := P ⋙ G
  have hnat : ∀ n k (h : n ≤ k), H.map (homOfLE h) ≫ z k = z n := by
    intro n k h
    induction k, h using Nat.le_induction with
    | base => simp [H]
    | succ k hk ih =>
      have hcat : homOfLE hk ≫ homOfLE (Nat.le_succ k) =
          homOfLE (hk.trans (Nat.le_succ k)) := Subsingleton.elim _ _
      have hstep : H.map (homOfLE (Nat.le_succ k)) ≫ z (k + 1) = z k := by
        change G.map (P.map (homOfLE (Nat.le_succ k))) ≫ z (k + 1) = z k
        rw [show P.map (homOfLE (Nat.le_succ k)) = homOfLE (hI k) from Subsingleton.elim _ _]
        exact hz k
      rw [← hcat, Functor.map_comp, Category.assoc, hstep, ih]
  let c : Cocone H :=
    { pt := Y
      ι :=
        { app := z
          naturality := by
            intro n k f
            rw [show f = homOfLE (leOfHom f) from Subsingleton.elim _ _]
            simpa using hnat n k (leOfHom f) } }
  refine ⟨(Functor.Final.colimitIso P G).inv ≫ colimit.desc H c, fun n => ?_⟩
  change colimit.ι G (P.obj n) ≫ (Functor.Final.colimitIso P G).inv ≫ colimit.desc H c = z n
  rw [← Category.assoc, Functor.Final.ι_colimitIso_inv P G n]
  exact colimit.ι_desc c n

end Colimit

section Truncations

/-- Restricting a section twice is restricting it along the composite. -/
private lemma map_map_of_comp {C : Type*} [Category C] (X : C ⥤ Type*) {a b c : C}
    {f : a ⟶ b} {g : b ⟶ c} {h : a ⟶ c} (hfg : f ≫ g = h) (x : X.obj a) :
    X.map g (X.map f x) = X.map h x := by
  subst hfg
  exact (Functor.map_comp_apply X f g x).symm

variable {R : Type u} [CommRing R] [IsLocalRing R]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Stacks 0AQH, read on truncations.** Let `R` be a Noetherian complete local ring, `J n` a
decreasing sequence of ideals contained in `𝔪`, cofinal with the powers of `𝔪`, and `X` an
algebraic space over `S`. Let `T` be an object of the site whose scheme is identified with
`Spec R`, and `W n` objects whose schemes are identified with `Spec (R ⧸ J n)`, mapping to `T`
by the quotient maps and to each other compatibly. Then a compatible family of sections of `X`
over the `W n` is the restriction of a unique section over `T`. -/
public theorem existsUnique_section_of_compatible_truncations
    (hR : IsNoetherianCompleteLocalRing R)
    (J : ℕ → Ideal R) (hJm : ∀ n, J n ≤ maximalIdeal R) (hJmono : ∀ n, J (n + 1) ≤ J n)
    (hJ₁ : ∀ n, ∃ k, maximalIdeal R ^ k ≤ J n) (hJ₂ : ∀ k, ∃ n, J n ≤ maximalIdeal R ^ k)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of R))
    (W : ℕ → BigFppfOver B S hS)
    (eW : ∀ n, (BigFppfOver.toScheme B S hS).obj (W n) ≅ Spec (.of (R ⧸ J n)))
    (ι : ∀ n, W n ⟶ T)
    (hι : ∀ n, (BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom =
      (eW n).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))))
    (τ : ∀ n, W n ⟶ W (n + 1)) (hτ : ∀ n, τ n ≫ ι (n + 1) = ι n)
    (x : ∀ n, X.obj (op (W n))) (hx : ∀ n, X.map (τ n).op (x (n + 1)) = x n) :
    ∃! y : X.obj (op T), ∀ n, X.map (ι n).op y = x n := by
  classical
  let : TopologicalSpace R := (maximalIdeal R).adicTopology
  let : NonarchimedeanRing R := (maximalIdeal R).nonarchimedean
  let : IsLinearTopology R R := (maximalIdeal R).isLinearTopology
  have : IsAdicComplete (maximalIdeal R) R := hR.isComplete
  have hRS : B.Contains (Spec (.of R)) := by
    change (Spec (.of R)).size < B.cutoff
    rw [← Scheme.size_congr eT]
    exact T.left.2
  let p : Spec (.of R) ⟶ S := eT.inv ≫ B.inclusion.map T.hom
  let D : QuotientSystem B S hS R := maximalIdealAdicQuotientSystem hRS p
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (specOver hRS p)
  -- the comparison of `T` with the spectrum of `R` in the site
  let t : T₀ ⟶ T := Over.homMk (ObjectProperty.homMk (X := B.obj hRS) (Y := T.left) eT.inv) rfl
  have ht : (BigFppfOver.toScheme B S hS).map t = eT.inv := rfl
  have : IsIso t := by
    have : IsIso ((BigFppfOver.toScheme B S hS).map t) := ht ▸ eT.isIso_inv
    exact isIso_of_reflects_iso t (BigFppfOver.toScheme B S hS)
  -- the weak ideals of definition of the sequence
  let Jw : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } := fun n =>
    ⟨J n, isWeakIdealOfDefinition_of_between_maximalIdeal_powers (J n) (hJ₁ n) (hJm n)⟩
  let stage : ∀ n, BigFppfOver B S hS := fun n =>
    (BigAffineFppf.inclusion B S hS).obj (D.stage (Jw n))
  have hmono : ∀ n, Mono ((BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom) := by
    intro n
    rw [hι n]
    have := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) Ideal.Quotient.mk_surjective
    infer_instance
  have hιs : ∀ n, (eW n).inv ≫ (BigFppfOver.toScheme B S hS).map (ι n) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) ≫ eT.inv := fun n => by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, hι n]
  have hsw : ∀ n, (eW n).inv ≫ B.inclusion.map (W n).hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) ≫ p := by
    intro n
    have hιS : (BigFppfOver.toScheme B S hS).map (ι n) ≫ B.inclusion.map T.hom =
        B.inclusion.map (W n).hom := by
      change B.inclusion.map ((ι n).left ≫ T.hom) = _
      rw [Over.w]
    rw [← hιS, ← Category.assoc, hιs n, Category.assoc]
  let s : ∀ n, stage n ⟶ W n := fun n =>
    Over.homMk (ObjectProperty.homMk (X := (stage n).left) (Y := (W n).left) (eW n).inv)
      (ObjectProperty.hom_ext _ (hsw n))
  have hs : ∀ n, (BigFppfOver.toScheme B S hS).map (s n) = (eW n).inv := fun n => rfl
  have hsiso : ∀ n, IsIso (s n) := by
    intro n
    have : IsIso ((BigFppfOver.toScheme B S hS).map (s n)) := (hs n) ▸ (eW n).isIso_inv
    exact isIso_of_reflects_iso (s n) (BigFppfOver.toScheme B S hS)
  have hstageT : ∀ n, (BigAffineFppf.inclusion B S hS).map
      (stageToSpec D hRS p (Jw n) rfl) ≫ t = s n ≫ ι n := by
    intro n
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, ht, hs n]
    exact (hιs n).symm
  let tr : ∀ n, OrderDual.toDual (Jw n) ⟶ OrderDual.toDual (Jw (n + 1)) := fun n =>
    homOfLE (show Jw (n + 1) ≤ Jw n from hJmono n)
  have hstage : ∀ n, (BigAffineFppf.inclusion B S hS).map
      (D.transition (J := Jw (n + 1)) (L := Jw n) (hJmono n)) ≫ s (n + 1) = s n ≫ τ n := by
    intro n
    apply (BigFppfOver.toScheme B S hS).map_injective
    have := hmono (n + 1)
    rw [← cancel_mono ((BigFppfOver.toScheme B S hS).map (ι (n + 1)) ≫ eT.hom)]
    have f₁ : (BigFppfOver.toScheme B S hS).map (s (n + 1)) ≫
        (BigFppfOver.toScheme B S hS).map (ι (n + 1)) ≫ eT.hom =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J (n + 1)))) := by
      rw [hs (n + 1), hι (n + 1)]
      exact (eW (n + 1)).inv_hom_id_assoc _
    have f₂ : (BigFppfOver.toScheme B S hS).map (τ n) ≫
        (BigFppfOver.toScheme B S hS).map (ι (n + 1)) ≫ eT.hom =
          (BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom := by
      rw [← Category.assoc, ← Functor.map_comp, hτ n]
    have f₃ : (BigFppfOver.toScheme B S hS).map (s n) ≫
        (BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) := by
      rw [hs n, hι n]
      exact (eW n).inv_hom_id_assoc _
    have e₁ : (BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map
          (D.transition (J := Jw (n + 1)) (L := Jw n) (hJmono n)) ≫ s (n + 1)) ≫
          (BigFppfOver.toScheme B S hS).map (ι (n + 1)) ≫ eT.hom =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) := by
      refine (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) f₁).trans ?_
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hJmono n))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J (n + 1)))) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
    have e₂ : (BigFppfOver.toScheme B S hS).map (s n ≫ τ n) ≫
          (BigFppfOver.toScheme B S hS).map (ι (n + 1)) ≫ eT.hom =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) := by
      rw [Functor.map_comp, Category.assoc, f₂, f₃]
    exact e₁.trans e₂.symm
  -- the sections over the stages
  let x' : ∀ n, X.obj (op (stage n)) := fun n => X.map (s n).op (x n)
  have hx' : ∀ n, X.map ((BigAffineFppf.inclusion B S hS).map
      (D.transition (J := Jw (n + 1)) (L := Jw n) (hJmono n))).op (x' (n + 1)) = x' n := by
    intro n
    refine (map_map_of_comp X (congrArg Quiver.Hom.op (hstage n)) (x (n + 1))).trans ?_
    exact (map_map_of_comp X rfl (x (n + 1))).symm.trans (congrArg (X.map (s n).op) (hx n))
  let z : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (Jw n)) ⟶
      upliftedSheaf X hX := fun n =>
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm (ULift.up (x' n))
  have hz : ∀ n, (formalSpectrumDiagram D).map (tr n) ≫ z (n + 1) = z n := by
    intro n
    have h : (upliftedSheaf X hX).obj.map ((BigAffineFppf.inclusion B S hS).map
        (D.transition (J := Jw (n + 1)) (L := Jw n) (hJmono n))).op (ULift.up (x' (n + 1))) =
          ULift.up (x' n) :=
      congrArg ULift.up (hx' n)
    refine Eq.trans ?_ (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm h)
    exact (Sheaf.sectionEquiv_symm_map (BigFppfOver.topology B S hS)
      ((BigAffineFppf.inclusion B S hS).map
        (D.transition (J := Jw (n + 1)) (L := Jw n) (hJmono n))) (F := upliftedSheaf X hX)
      (ULift.up (x' (n + 1)))).symm
  have hcof : ∀ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, (Jw n).1 ≤ L.1 := by
    intro L
    obtain ⟨k, hk⟩ := exists_maximalIdeal_pow_le_of_isWeakIdealOfDefinition L.1 L.2
    exact (hJ₂ k).imp fun _ hn => hn.trans hk
  obtain ⟨q, hq⟩ := exists_formalSpectrum_desc_of_decreasing_cofinal D Jw
    (fun n => show Jw (n + 1) ≤ Jw n from hJmono n) hcof z hz
  have hD₁ : ∀ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ L.1 :=
    fun L => exists_maximalIdeal_pow_le_of_isWeakIdealOfDefinition L.1 L.2
  have hD₂ : ∀ n : ℕ, ∃ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      L.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n :=
    fun n => ⟨⟨maximalIdeal R ^ (n + 1),
      isWeakIdealOfDefinition_of_between_maximalIdeal_powers _ ⟨n + 1, le_rfl⟩
        (Ideal.pow_le_self (Nat.succ_ne_zero n))⟩, Ideal.pow_le_pow_right (Nat.le_succ n)⟩
  obtain ⟨f, hf⟩ := (bijective_map_into_algebraicSpace hR D hD₁ hD₂ hRS p (fun _ => rfl)
    X hX).2 q
  let y₀ : X.obj (op T₀) := (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) f).down
  have hres : ∀ n, X.map ((BigAffineFppf.inclusion B S hS).map
      (stageToSpec D hRS p (Jw n) rfl)).op y₀ = x' n := by
    intro n
    have h₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS p (Jw n) rfl)) ≫ f = z n := by
      rw [← formalSpectrumToSpec_spec D hRS p (fun _ => rfl) (Jw n)]
      exact (Category.assoc _ _ _).trans ((congrArg _ hf).trans (hq n))
    have h₃ := congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) h₂
    rw [Sheaf.sectionEquiv_map_comp] at h₃
    exact congrArg ULift.down (h₃.trans (Equiv.apply_symm_apply _ _))
  have hinj : ∀ n, Function.Injective (X.map (s n).op) := by
    intro n a b hab
    have := hsiso n
    simpa only [← Functor.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
      Functor.map_id_apply] using congrArg (X.map (inv (s n)).op) hab
  refine ⟨X.map (inv t).op y₀, fun n => ?_, fun y hy => ?_⟩
  · apply hinj n
    refine (map_map_of_comp X rfl _).trans ?_
    refine (map_map_of_comp X (f := (inv t).op) (g := (s n ≫ ι n).op)
      (h := ((BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS p (Jw n) rfl)).op)
      ?_ y₀).trans (hres n)
    rw [← hstageT n, op_comp, ← Category.assoc, ← op_comp, IsIso.hom_inv_id, op_id,
      Category.id_comp]
  · have key : X.map t.op y = y₀ := by
      refine eq_of_forall_quotientPow_factorization hX (maximalIdeal.isMaximal R)
        (fun k => ?_)
      obtain ⟨n, hn⟩ := hJ₂ k
      refine ⟨stage n, (BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS p (Jw n) rfl),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hn)), ?_, ?_⟩
      · change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hn)) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))) = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
      · rw [hres n]
        refine (map_map_of_comp X (congrArg Quiver.Hom.op (hstageT n)) y).trans ?_
        exact (map_map_of_comp X rfl y).symm.trans (congrArg (X.map (s n).op) (hy n))
    rw [← key]
    refine ((map_map_of_comp X (f := t.op) (g := (inv t).op) (h := 𝟙 _) ?_ y).trans
      (X.map_id_apply _ y)).symm
    rw [← op_comp, IsIso.inv_hom_id, op_id]

end Truncations

end AlgebraicGeometry.FormalSpace

end

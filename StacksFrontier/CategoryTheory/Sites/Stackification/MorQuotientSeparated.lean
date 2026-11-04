module

public import StacksFrontier.CategoryTheory.Sites.Stackification.MorQuotient

/-! # The quotient by local equality is separated

This file supplies the *reduction* that the first stage of the construction of the
stackification of a fibred category is for. Having formed the quotient
`CategoryTheory.Functor.MorQuotient p J` of a fibred category `p : 𝒳 ⥤ 𝒮` by local equality
of morphisms, one must know that nothing is left to quotient: two locally equal morphisms of
the quotient are already equal. The source records this as "thus we reduce to the case where
locally equal morphisms are equal".

This is not a formal consequence of the construction. Two morphisms `F`, `G` of the quotient
that are locally equal lift to morphisms `f`, `g` of `𝒳` whose restrictions along a covering
sieve are only *locally* equal, one covering sieve for each member. Concluding that `f` and
`g` are locally equal over a single sieve is exactly the local character (transitivity) of
the Grothendieck topology, applied to the sieve

`CategoryTheory.Functor.agreementSieve`

of morphisms of the base along which `f` and `g` genuinely agree. That this collection *is*
a sieve is where fibredness of `p` enters: an arbitrary morphism into the source of `f` over
a member of the sieve has to be factored through a strongly cartesian morphism.

## Main definitions

* `CategoryTheory.Functor.agreementSieve`: the sieve of morphisms of the base along which
  two morphisms of `𝒳` with the same source agree after restriction.

## Main results

* `CategoryTheory.Functor.locallyEqual_morQuotientProj_iff`: local equality in
  `MorQuotient p J` is equality. Equivalently, the morphism presheaves of the quotient are
  separated.

## References

The reduction closing the first stage of the proof of Stacks 02ZN.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

variable {p : 𝒳 ⥤ 𝒮} {J : GrothendieckTopology 𝒮}

/-- Given two morphisms `f g : x ⟶ y` of `𝒳`, the *agreement sieve* of `f` and `g` consists
of those morphisms `h : V ⟶ p.obj x` of the base such that `f` and `g` agree after
restricting `x` along `h`, in the strong sense that `ρ ≫ f = ρ ≫ g` for every morphism
`ρ` into `x` whose image factors through `h`.

Phrasing membership with an explicit factorisation `p.map ρ = k ≫ h`, rather than with
`p.map ρ = h` on the nose, is what makes downward closure hold for formal reasons: it is
absorbed into `k`. -/
@[implicit_reducible]
def agreementSieve (p : 𝒳 ⥤ 𝒮) {x y : 𝒳} (f g : x ⟶ y) : Sieve (p.obj x) where
  arrows V h := ∀ ⦃w : 𝒳⦄ (ρ : w ⟶ x) (k : p.obj w ⟶ V), p.map ρ = k ≫ h → ρ ≫ f = ρ ≫ g
  downward_closed := by
    intro V V' h hh k₀ w ρ k hk
    exact hh ρ (k ≫ k₀) (by rw [hk, assoc])

/-- Membership in the agreement sieve of `f` and `g`, unfolded: `h` belongs to it exactly when
`ρ ≫ f = ρ ≫ g` for every `ρ` into `x` whose image factors through `h`. -/
theorem mem_agreementSieve_iff (p : 𝒳 ⥤ 𝒮) {x y : 𝒳} (f g : x ⟶ y) {V : 𝒮}
    (h : V ⟶ p.obj x) :
    (agreementSieve p f g).arrows h ↔
      ∀ ⦃w : 𝒳⦄ (ρ : w ⟶ x) (k : p.obj w ⟶ V), p.map ρ = k ≫ h → ρ ≫ f = ρ ≫ g :=
  Iff.rfl

/-- A morphism whose image lies in the agreement sieve equalises `f` and `g`. -/
theorem eq_comp_of_mem_agreementSieve {x y : 𝒳} {f g : x ⟶ y} {w : 𝒳} (ρ : w ⟶ x)
    (hρ : (agreementSieve p f g).arrows (p.map ρ)) : ρ ≫ f = ρ ≫ g :=
  (mem_agreementSieve_iff p f g _).mp hρ ρ (𝟙 _) (by rw [id_comp])

/-- **The quotient by local equality is separated**: two locally equal morphisms of
`MorQuotient p J` are equal.

This is the reduction the first stage of the construction of the stackification exists to
achieve. The proof runs as follows. Lift the two morphisms to morphisms `f`, `g` of `𝒳`.
The hypothesis provides a covering sieve `S` of the base such that, for each member `h` of
`S`, the restrictions of `f` and `g` along the chosen strongly cartesian lift of `h` become
equal *in the quotient* — hence are only locally equal in `𝒳`, over some further covering
sieve `T` depending on `h`. To assemble these into a single covering sieve, note that each
such `T` is contained in the pullback along `h` of the agreement sieve of `f` and `g`; so
that pullback is covering for every `h ∈ S`, and the local character of the topology makes
the agreement sieve itself covering. -/
theorem locallyEqual_morQuotientProj_iff [p.IsFibered] {A B : p.MorQuotient J} (F G : A ⟶ B) :
    (p.morQuotientProj J).LocallyEqual J F G ↔ F = G := by
  refine ⟨fun h ↦ ?_, locallyEqual_of_eq⟩
  obtain ⟨f, hf⟩ := exists_eq_toMorQuotient_map F
  obtain ⟨g, hg⟩ := exists_eq_toMorQuotient_map G
  subst hf
  subst hg
  obtain ⟨hbase, S, hS, hagree⟩ := h
  refine (CategoryTheory.Quotient.functor_map_eq_iff (p.locallyEqualRel J) _ _).mpr ?_
  -- The agreement sieve of `f` and `g` is covering, by the local character of `J`.
  have hRag : agreementSieve p f g ∈ J (p.obj A.as) := by
    refine J.transitive hS _ fun V h hh ↦ ?_
    -- The chosen strongly cartesian lift of `h`.
    have ha : p.obj A.as = p.obj A.as := rfl
    have hprj : p.obj (IsPreFibered.pullbackObj ha h) = V := IsPreFibered.pullbackObj_proj ha h
    set ψ := IsPreFibered.pullbackMap ha h with hψdef
    have hcart : p.IsStronglyCartesian h ψ := inferInstance
    have hmapψ : p.map ψ = eqToHom hprj ≫ h := by
      have := IsHomLift.fac' p h ψ
      simpa using this
    -- `ψ` lies over a member of `S`, so `f` and `g` agree after restriction along it in the
    -- quotient, hence are locally equal in `𝒳` over some covering sieve `T`.
    have hmemS : S.arrows (p.map ψ) := by
      rw [hmapψ]; exact S.downward_closed hh _
    have hquot : (p.toMorQuotient J).map (ψ ≫ f) = (p.toMorQuotient J).map (ψ ≫ g) := by
      rw [Functor.map_comp, Functor.map_comp]
      exact hagree ((p.toMorQuotient J).map ψ) hmemS
    obtain ⟨-, T, hT, hagree'⟩ :=
      (CategoryTheory.Quotient.functor_map_eq_iff (p.locallyEqualRel J) (ψ ≫ f) (ψ ≫ g)).mp hquot
    -- Transport `T` to a covering sieve of `V` and compare it with the agreement sieve.
    refine J.superset_covering (S := T.pullback (eqToHom hprj.symm)) ?_
      (J.pullback_stable _ hT)
    intro V' k hk
    rw [Sieve.pullback_apply] at hk
    rw [Sieve.pullback_apply, mem_agreementSieve_iff]
    intro w ρ k₁ hk₁
    -- Factor `ρ` through `ψ`.
    have hfac : p.map ρ = (k₁ ≫ k) ≫ h := by rw [hk₁, assoc]
    set σ := IsStronglyCartesian.map p h ψ hfac ρ with hσdef
    have hσfac : σ ≫ ψ = ρ := IsStronglyCartesian.fac ..
    have hσlift : p.IsHomLift (k₁ ≫ k) σ := inferInstance
    have hmapσ : p.map σ = (k₁ ≫ k) ≫ eqToHom hprj.symm := by
      simpa using IsHomLift.fac' p (k₁ ≫ k) σ
    have hmemT : T.arrows (p.map σ) := by
      rw [hmapσ, assoc]
      exact T.downward_closed hk _
    have := hagree' σ hmemT
    rwa [← assoc, ← assoc, hσfac] at this
  exact ⟨hbase, agreementSieve p f g, hRag, fun _ ρ hρ ↦ eq_comp_of_mem_agreementSieve ρ hρ⟩

/-- Restated without reference to the relation: if the classes of `f` and `g` in the
quotient are locally equal, then `f` and `g` were already locally equal. So local equality
is idempotent as a construction, which is the precise sense in which the first stage of the
stackification is a reduction. -/
theorem locallyEqual_of_locallyEqual_toMorQuotient_map [p.IsFibered] {x y : 𝒳} {f g : x ⟶ y}
    (h : (p.morQuotientProj J).LocallyEqual J ((p.toMorQuotient J).map f)
      ((p.toMorQuotient J).map g)) :
    p.LocallyEqual J f g :=
  (CategoryTheory.Quotient.functor_map_eq_iff (p.locallyEqualRel J) f g).mp
    ((locallyEqual_morQuotientProj_iff _ _).mp h)

end CategoryTheory.Functor

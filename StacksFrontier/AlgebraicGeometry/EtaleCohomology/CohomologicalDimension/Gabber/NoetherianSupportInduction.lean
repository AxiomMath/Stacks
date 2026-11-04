module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.OpenPairSupport
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberInputs

/-!
# Exposé XVIII-A, Lemma 2.2: the Noetherian induction on supports

Let `X` be a Noetherian scheme on which `n` is invertible and `c : X → WithBot ℕ∞` a function
bounding the cohomology of the residue fields with coefficients killed by `n`. Write
`b(x) = c(x) + 2 dim 𝒪_{X,x}`. Lemma 2.2 of Travaux de Gabber, Exposé XVIII-A, says that
`sup_x b(x)` bounds the cohomology of `X` with coefficients killed by `n`
(`AlgebraicGeometry.Scheme.LocalToGlobalVanishingBound`). This file proves it from a purely local
statement at one point, by the source's induction with supports.

**The local statement** (`AlgebraicGeometry.Scheme.GenericPointSupportKilling`): if `η` is a
maximal point of the closed set `T = X ∖ U` (no point of `T` other than `η` generalizes `η`) and
`b(η) < i`, then every class in `H^i_T(X, 𝓕)` vanishes after restriction to some open
neighbourhood `V` of `η`, in `H^i_{T ∩ V}(V, 𝓕)`. In the source this is the computation of
`H^i_η(Spec 𝒪_{X,η}, 𝓕)` through the strict henselization and the punctured bound.

**The induction**
(`AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_of_genericPointSupportKilling`):
`H^i_T(X, 𝓕) = 0` for `i > sup_{t ∈ T} b(t)`, by Noetherian induction on the closed set `T`. For
`T` nonempty pick a maximal point `η` of `T`; a class `ξ` dies on a neighbourhood `V` of `η`; by
excision `H^i_{T ∩ V}(V) = H^i_{T ∩ V}(X ∖ T')` with `T' = T ∖ V`, so `ξ` dies in
`H^i_{T∖T'}(X ∖ T')`, hence comes from `H^i_{T'}(X)`, which vanishes by induction since
`T' ⊊ T`. The case `T = X` is the lemma.

## Main definitions

* `AlgebraicGeometry.Scheme.GenericPointSupportKilling`: the local statement.

## Main results

* `AlgebraicGeometry.Scheme.exists_mem_forall_mem_closure_eq`: a nonempty closed subset of a
  Noetherian quasi-sober `T₀` space has a maximal point.
* `AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_of_genericPointSupportKilling`: the
  vanishing with supports.
* `AlgebraicGeometry.Scheme.localToGlobalVanishingBound_of_genericPointSupportKilling`:
  Lemma 2.2 from the local statement.

## References

* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber, Exposé XVIII-A,
  Lemma 2.2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- **A nonempty closed subset of a Noetherian quasi-sober `T₀` space has a maximal point**: a
point `η ∈ T` which is generalized by no other point of `T`. Take a component of `T` maximal
among the finitely many irreducible closed sets covering `T`, and its generic point. -/
theorem exists_mem_forall_mem_closure_eq {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    [QuasiSober α] [T0Space α] {T : Set α} (hT : IsClosed T) (hne : T.Nonempty) :
    ∃ η ∈ T, ∀ x ∈ T, η ∈ closure ({x} : Set α) → x = η := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨t, ht, -⟩ := Set.mem_sUnion.1 hy
    exact ⟨t, ht⟩
  obtain ⟨C, hCmax⟩ := hSf.exists_maximal hSne
  have hCS : C ∈ S := hCmax.prop
  have hη : IsGenericPoint (hSirr C hCS).genericPoint C := by
    have := (hSirr C hCS).isGenericPoint_genericPoint_closure
    rwa [(hScl C hCS).closure_eq] at this
  refine ⟨(hSirr C hCS).genericPoint, Set.mem_sUnion.2 ⟨C, hCS, hη.mem⟩, fun x hx hηx => ?_⟩
  obtain ⟨C', hC'S, hxC'⟩ := Set.mem_sUnion.1 hx
  have h1 : C ⊆ closure ({x} : Set α) := by
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hηx) isClosed_closure
  have h2 : closure ({x} : Set α) ⊆ C' :=
    closure_minimal (Set.singleton_subset_iff.2 hxC') (hScl C' hC'S)
  have h3 : C' ⊆ C := hCmax.2 hC'S (h1.trans h2)
  have h4 : closure ({x} : Set α) = closure {(hSirr C hCS).genericPoint} := by
    rw [hη.def]
    exact (h2.trans h3).antisymm h1
  exact (inseparable_iff_closure_eq.2 h4).eq

/-- **The local statement of the dévissage.** For a Noetherian scheme `X` on which `n` is
invertible, an open `U ⊆ X`, a maximal point `η` of `X ∖ U`, a bound `c` for the cohomology of
`Spec κ(η)` with coefficients killed by `n`, an abelian sheaf `𝓕` on `X_ét` killed by `n` and
`i > c + 2 dim 𝒪_{X,η}`: every class of `H^i_{X∖U}(X, 𝓕)` restricts to zero in
`H^i_{V∖U}(V, 𝓕)` for some open neighbourhood `V` of `η`. -/
def GenericPointSupportKilling (n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], IsUnit (n : Γ(X, ⊤)) →
    ∀ (U : X.Opens) (η : X), η ∉ U → (∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η) →
      ∀ c : WithBot ℕ∞, IsTorsionVanishingBound (Spec (.of (X.residueField η))) n c →
        ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
          (∀ (T : X.Etale) (x : F.obj.obj (op T)), n • x = 0) →
            ∀ i : ℕ, c + 2 * ringKrullDim (X.presheaf.stalk η) < i →
              ∀ ξ : ((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F,
                ∃ V : X.Opens, η ∈ V ∧
                  (NatTrans.rightDerived (opensSupportRestrict (le_top : U ≤ ⊤)
                    (inf_le_left : V ⊓ U ≤ V) le_top inf_le_right) i).app F ξ = 0

variable {n : ℕ}

/-- **Exposé XVIII-A, Lemma 2.2, with supports**, from the local statement: for every open
`U ⊆ X`, `H^i_{X∖U}(X, 𝓕) = 0` as soon as `i > sup_{t ∉ U} (c(t) + 2 dim 𝒪_{X,t})`. -/
theorem isZero_rightDerived_opensSupport_of_genericPointSupportKilling
    (h : GenericPointSupportKilling.{u} n) (X : Scheme.{u}) [IsNoetherian X]
    (hn : IsUnit (n : Γ(X, ⊤))) (c : X → WithBot ℕ∞)
    (hc : ∀ x, IsTorsionVanishingBound (Spec (.of (X.residueField x))) n (c x))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (T : X.Etale) (x : F.obj.obj (op T)), n • x = 0) (U : X.Opens) :
    ∀ i : ℕ, (⨆ (x : X) (_ : x ∉ U), (c x + 2 * ringKrullDim (X.presheaf.stalk x))) < i →
      IsZero (((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F) := by
  induction U using WellFoundedGT.induction with
  | ind U ih =>
  intro i hi
  by_cases hU : U = ⊤
  · subst hU
    exact isZero_rightDerived_opensSupport_self ⊤ F i
  obtain ⟨η, hηT, hηmax⟩ := exists_mem_forall_mem_closure_eq (T := ((U : Set X)ᶜ))
    U.isOpen.isClosed_compl (by
      by_contra hne
      exact hU (Opens.ext (Set.compl_empty_iff.1 (Set.not_nonempty_iff_eq_empty.1 hne))))
  have hb : c η + 2 * ringKrullDim (X.presheaf.stalk η) < i :=
    lt_of_le_of_lt (le_iSup₂ (f := fun (x : X) (_ : x ∉ U) =>
      c x + 2 * ringKrullDim (X.presheaf.stalk x)) η hηT) hi
  suffices hξ : ∀ ξ : ((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F, ξ = 0 by
    have : Subsingleton (((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F) :=
      ⟨fun a b => (hξ a).trans (hξ b).symm⟩
    exact AddCommGrpCat.isZero_of_subsingleton _
  intro ξ
  obtain ⟨V, hηV, hV⟩ := h X hn U η hηT (fun x hx hxU => hηmax x hxU hx) (c η) (hc η) F hF i hb ξ
  have hlt : U < U ⊔ V := by
    refine lt_of_le_of_ne le_sup_left fun he => hηT ?_
    rw [he]
    exact (le_sup_right : V ≤ U ⊔ V) hηV
  have hi' : (⨆ (x : X) (_ : x ∉ U ⊔ V), (c x + 2 * ringKrullDim (X.presheaf.stalk x))) < i :=
    lt_of_le_of_lt (iSup₂_le fun x hx => le_iSup₂ (f := fun (x : X) (_ : x ∉ U) =>
      c x + 2 * ringKrullDim (X.presheaf.stalk x)) x
        fun hxU => hx ((le_sup_left : U ≤ U ⊔ V) hxU)) hi
  have hzero := ih (U ⊔ V) hlt i hi'
  have hcomp := opensSupportRestrict_comp (le_top : U ≤ ⊤) (le_sup_left : U ≤ U ⊔ V)
    (inf_le_left : V ⊓ U ≤ V) (le_top : U ⊔ V ≤ ⊤) (le_refl U) (le_sup_right : V ≤ U ⊔ V)
    (inf_le_right : V ⊓ U ≤ U)
  have h2 : (NatTrans.rightDerived (opensSupportRestrict (le_top : U ≤ ⊤)
      (le_sup_left : U ≤ U ⊔ V) (le_top : U ⊔ V ≤ ⊤) (le_refl U)) i).app F ξ = 0 := by
    have hiso : IsIso ((NatTrans.rightDerived (opensSupportRestrict (le_sup_left : U ≤ U ⊔ V)
        (inf_le_left : V ⊓ U ≤ V) (le_sup_right : V ≤ U ⊔ V) (inf_le_right : V ⊓ U ≤ U)) i).app
          F) :=
      Iso.isIso_hom ((Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso
        (asIso (opensSupportRestrict (le_sup_left : U ≤ U ⊔ V) (inf_le_left : V ⊓ U ≤ V)
          (le_sup_right : V ≤ U ⊔ V) (inf_le_right : V ⊓ U ≤ U))) i).app F)
    apply ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1
    rw [map_zero, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← NatTrans.rightDerived_comp, hcomp]
    exact hV
  obtain ⟨y, hy⟩ := exists_rightDerived_opensSupportRestrict_eq (le_sup_left : U ≤ U ⊔ V)
    (le_top : U ⊔ V ≤ ⊤) F i ξ h2
  rw [← hy, (AddCommGrpCat.subsingleton_of_isZero hzero).elim y 0, map_zero]

/-- **Exposé XVIII-A, Lemma 2.2** (`AlgebraicGeometry.Scheme.LocalToGlobalVanishingBound`), from
the local statement `AlgebraicGeometry.Scheme.GenericPointSupportKilling`: the case `U = ∅` of
the vanishing with supports. -/
theorem localToGlobalVanishingBound_of_genericPointSupportKilling
    (h : GenericPointSupportKilling.{u} n) : LocalToGlobalVanishingBound.{u} n := by
  intro X _ hn c hc G hG p hp
  apply subsingleton_sheafH_of_isZero_rightDerived_opensSupport_bot
  refine isZero_rightDerived_opensSupport_of_genericPointSupportKilling h X hn c hc G hG ⊥ p ?_
  exact lt_of_le_of_lt (iSup₂_le fun x _ => le_iSup (fun x : X =>
    c x + 2 * ringKrullDim (X.presheaf.stalk x)) x) hp

end AlgebraicGeometry.Scheme

end

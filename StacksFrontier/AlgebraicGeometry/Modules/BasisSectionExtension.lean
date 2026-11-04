module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# Extending a comparison of sheaves of modules from a basis of an open

Let `M` and `N` be sheaves of modules on a scheme `S`, let `T` be an open of `S`, and let
`W : κ → S.Opens` be a family of opens of `S` contained in `T` which is a basis of `T`: every
point of every open contained in `T` has a member of the family around it inside that open.
Given `Γ(S, W k)`-linear identifications `Γ(M, W k) ≃ Γ(N, W k)` compatible with the restriction
maps, this file produces identifications `Γ(M, V) ≃ Γ(N, V)` for *every* open `V ≤ T`, compatible
with all restriction maps and agreeing with the given ones on the basis.

This is the input that `Stacks.SheafOfModules.ModulesGlueData` requires of an overlap comparison:
its `trans` field is indexed by an arbitrary open of the overlap, while a comparison of two
quasi-coherent sheaves is usually only available on a basis of affine opens.

## Main results

* `Stacks.Modules.sections_eq_of_basis`: two sections over an open `V ≤ T` agreeing on every
  member of the basis contained in `V` are equal. This is the separation half of the sheaf
  axiom read along the basis.
* `Stacks.Modules.sectionsMap_eq_of_basis`: two restriction-compatible families of maps on the
  opens contained in `T` agreeing on the basis are equal. This is what makes the extension
  below canonical, and is how a cocycle identity for extended comparisons is proved.
* `Stacks.Modules.exists_sectionEquiv_of_basis`: the extension itself.

## Implementation notes

Opens are indexed as opens of `S` lying below `T`, never as opens of the open subscheme
`T.toScheme`, so no statement here transports along an identification of opens. (The absolute
case — a basis of the whole space — is already available as
`Stacks.Veronese.exists_moduleSheafIso_of_sectionIso_onBasis`, but using it on `T.toScheme` forces
the identification `T.ι ''ᵁ T.ι ⁻¹ᵁ V = V`, which is a propositional equality of opens.)

The construction is the usual one: for an open `V ≤ T` and a section `s` of `M` over `V`, the
images of the restrictions of `s` under the basis identifications form a compatible family on the
cover of `V` by the basis opens inside it, so the sheaf axiom for `N` glues them to a single
section. Compatibility of that family is itself proved by separation for `N`, on the basis cover
of an intersection of two basis opens — which is why the hypothesis on the family needs to be
stated only for an *inclusion* of two basis opens, and not on intersections (which need not be
basis opens).

Additivity, linearity, naturality and bijectivity of the resulting maps all follow from
separation on the same covers.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u v

namespace Stacks.Modules

variable {S : Scheme.{u}}

/-- Restriction of sections of a sheaf of modules along two composable inclusions of opens is
restriction along their composite; the inclusion is determined by the pair of opens. -/
public lemma res_comp (M : S.Modules) {A B C : S.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C)
    (s : Γ(M, C)) :
    M.presheaf.map i.op (M.presheaf.map j.op s) = M.presheaf.map k.op s := by
  have hk : k = i ≫ j := Subsingleton.elim _ _
  subst hk
  change ((M.presheaf.map j.op) ≫ (M.presheaf.map i.op)).hom s =
    (M.presheaf.map (i ≫ j).op).hom s
  rw [show (i ≫ j).op = j.op ≫ i.op from Subsingleton.elim _ _, ← M.presheaf.map_comp]

section

variable {M N : S.Modules} {T : S.Opens} {κ : Type v} {W : κ → S.Opens}

/-- The members of the basis contained in an open `V ≤ T` cover `V`. -/
private lemma le_iSup_basis
    (hb : ∀ V : S.Opens, V ≤ T → ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    {V : S.Opens} (hV : V ≤ T) :
    V ≤ ⨆ j : {k : κ // W k ≤ V}, W j.1 := by
  intro x hx
  obtain ⟨k, hxk, hkV⟩ := hb V hV x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, hkV⟩, hxk⟩

/-- **Separation along a basis of an open.** Two sections of a sheaf of modules over an open `V`
contained in `T` which agree on every basis open contained in `V` are equal. -/
public lemma sections_eq_of_basis (N : S.Modules)
    (hb : ∀ V : S.Opens, V ≤ T → ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    {V : S.Opens} (hV : V ≤ T) (s t : Γ(N, V))
    (h : ∀ (k : κ) (hk : W k ≤ V),
      N.presheaf.map (homOfLE hk).op s = N.presheaf.map (homOfLE hk).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab S)
    (fun j : {k : κ // W k ≤ V} => W j.1) V (fun j => homOfLE j.2)
    (le_iSup_basis hb hV) s t (fun j => h j.1 j.2)

/-- **A restriction-compatible family of maps is determined by its values on a basis.** Two
families of maps on the sections over the opens contained in `T`, each compatible with the
restriction maps, which agree on every basis open, agree on every open contained in `T`. -/
public lemma sectionsMap_eq_of_basis (M N : S.Modules)
    (hb : ∀ V : S.Opens, V ≤ T → ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    (Φ Ψ : ∀ V : S.Opens, V ≤ T → Γ(M, V) → Γ(N, V))
    (hΦ : ∀ (V V' : S.Opens) (hV : V ≤ T) (hV' : V' ≤ T) (h : V' ≤ V) (s : Γ(M, V)),
      Φ V' hV' (M.presheaf.map (homOfLE h).op s) =
        N.presheaf.map (homOfLE h).op (Φ V hV s))
    (hΨ : ∀ (V V' : S.Opens) (hV : V ≤ T) (hV' : V' ≤ T) (h : V' ≤ V) (s : Γ(M, V)),
      Ψ V' hV' (M.presheaf.map (homOfLE h).op s) =
        N.presheaf.map (homOfLE h).op (Ψ V hV s))
    (hagree : ∀ (k : κ) (hk : W k ≤ T) (s : Γ(M, W k)), Φ (W k) hk s = Ψ (W k) hk s)
    {V : S.Opens} (hV : V ≤ T) (s : Γ(M, V)) :
    Φ V hV s = Ψ V hV s := by
  refine sections_eq_of_basis N hb hV _ _ fun k hk => ?_
  rw [← hΦ V (W k) hV (hk.trans hV) hk s, ← hΨ V (W k) hV (hk.trans hV) hk s]
  exact hagree k (hk.trans hV) _

/-- The images under the basis maps of the restrictions of a section form a compatible family on
the cover of its open by the basis opens inside it. -/
private lemma basisFamily_isCompatible
    (hb : ∀ V : S.Opens, V ≤ T → ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    (φ : ∀ k, Γ(M, W k) → Γ(N, W k))
    (hφ : ∀ (k l : κ) (h : W l ≤ W k) (s : Γ(M, W k)),
      φ l (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ k s))
    {V : S.Opens} (hV : V ≤ T) (s : Γ(M, V)) :
    TopCat.Presheaf.IsCompatible (C := Ab) N.presheaf
      (fun j : {k : κ // W k ≤ V} => W j.1)
      (fun j => φ j.1 (M.presheaf.map (homOfLE j.2).op s)) := by
  intro j j'
  change N.presheaf.map (Opens.infLELeft (W j.1) (W j'.1)).op
        (φ j.1 (M.presheaf.map (homOfLE j.2).op s)) =
      N.presheaf.map (Opens.infLERight (W j.1) (W j'.1)).op
        (φ j'.1 (M.presheaf.map (homOfLE j'.2).op s))
  -- restricting a basis image of a restricted section further to a smaller basis open
  have key : ∀ (l : κ) (hl : W l ≤ V) (k : κ) (hk : W k ≤ W l),
      N.presheaf.map (homOfLE hk).op (φ l (M.presheaf.map (homOfLE hl).op s)) =
        φ k (M.presheaf.map (homOfLE (hk.trans hl)).op s) := fun l hl k hk => by
    rw [← hφ l k hk, res_comp M]
  refine sections_eq_of_basis N hb (V := W j.1 ⊓ W j'.1)
    (inf_le_left.trans (j.2.trans hV)) _ _ fun k hk => ?_
  rw [res_comp N (homOfLE hk) (Opens.infLELeft (W j.1) (W j'.1)) (homOfLE (hk.trans inf_le_left)),
    res_comp N (homOfLE hk) (Opens.infLERight (W j.1) (W j'.1))
      (homOfLE (hk.trans inf_le_right)),
    key j.1 j.2 k (hk.trans inf_le_left), key j'.1 j'.2 k (hk.trans inf_le_right)]

/-- The glued image of a section: the unique section of `N` whose restriction to each basis open
inside the given open is the basis map applied to the restriction of the section. -/
private lemma exists_glue
    (hb : ∀ V : S.Opens, V ≤ T → ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    (φ : ∀ k, Γ(M, W k) → Γ(N, W k))
    (hφ : ∀ (k l : κ) (h : W l ≤ W k) (s : Γ(M, W k)),
      φ l (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ k s))
    {V : S.Opens} (hV : V ≤ T) (s : Γ(M, V)) :
    ∃! t : Γ(N, V), ∀ (k : κ) (hk : W k ≤ V),
      N.presheaf.map (homOfLE hk).op t = φ k (M.presheaf.map (homOfLE hk).op s) := by
  obtain ⟨t, ht, huniq⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab S)
    (fun j : {k : κ // W k ≤ V} => W j.1) V (fun j => homOfLE j.2)
    (le_iSup_basis hb hV) _ (basisFamily_isCompatible hb φ hφ hV s)
  exact ⟨t, fun k hk => ht ⟨k, hk⟩, fun t' ht' => huniq t' fun j => ht' j.1 j.2⟩


/-- The glued image of a section: a section of `N` whose restriction to each basis open
inside the given open is the basis map applied to the restriction of the section. -/
private lemma exists_glue_map
    (hb : ∀ V : S.Opens, V ≤ T → ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    (φ : ∀ k, Γ(M, W k) → Γ(N, W k))
    (hφ : ∀ (k l : κ) (h : W l ≤ W k) (s : Γ(M, W k)),
      φ l (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ k s)) :
    ∃ F : ∀ V : S.Opens, V ≤ T → Γ(M, V) → Γ(N, V),
      ∀ (V : S.Opens) (hV : V ≤ T) (s : Γ(M, V)) (k : κ) (hk : W k ≤ V),
        N.presheaf.map (homOfLE hk).op (F V hV s) = φ k (M.presheaf.map (homOfLE hk).op s) := by
  choose F hF using fun (V : S.Opens) (hV : V ≤ T) (s : Γ(M, V)) =>
    (TopCat.Sheaf.existsUnique_gluing' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab S)
      (fun j : {k : κ // W k ≤ V} => W j.1) V (fun j => homOfLE j.2)
      (le_iSup_basis hb hV) _ (basisFamily_isCompatible hb φ hφ hV s)).exists
  exact ⟨F, fun V hV s k hk => hF V hV s ⟨k, hk⟩⟩

/-- **Extension of a comparison from a basis of an open.** `Γ(S, W k)`-linear identifications of
the sections of two sheaves of modules over the members of a basis of an open `T`, compatible with
the restriction maps, extend to `Γ(S, V)`-linear identifications over every open `V ≤ T`,
compatible with all restriction maps and agreeing with the given ones on the basis. -/
public theorem exists_sectionEquiv_of_basis (M N : S.Modules) (T : S.Opens) (W : κ → S.Opens)
    (hb : ∀ V : S.Opens, V ≤ T → ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    (e : ∀ k, Γ(M, W k) ≃ₗ[Γ(S, W k)] Γ(N, W k))
    (he : ∀ (k l : κ) (h : W l ≤ W k) (s : Γ(M, W k)),
      e l (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (e k s)) :
    ∃ E : ∀ V : S.Opens, V ≤ T → (Γ(M, V) ≃ₗ[Γ(S, V)] Γ(N, V)),
      (∀ (V V' : S.Opens) (hV : V ≤ T) (hV' : V' ≤ T) (h : V' ≤ V) (s : Γ(M, V)),
        E V' hV' (M.presheaf.map (homOfLE h).op s) =
          N.presheaf.map (homOfLE h).op (E V hV s)) ∧
      (∀ (k : κ) (hk : W k ≤ T) (s : Γ(M, W k)), E (W k) hk s = e k s) := by
  classical
  -- the comparison in the reverse direction satisfies the same compatibility
  have hesymm : ∀ (k l : κ) (h : W l ≤ W k) (t : Γ(N, W k)),
      (e l).symm (N.presheaf.map (homOfLE h).op t) =
        M.presheaf.map (homOfLE h).op ((e k).symm t) := by
    intro k l h t
    refine (e l).injective ?_
    rw [(e l).apply_symm_apply, he k l h ((e k).symm t), (e k).apply_symm_apply]
  obtain ⟨F, hFres⟩ := exists_glue_map hb (fun k s => e k s) he
  obtain ⟨G, hGres⟩ := exists_glue_map hb (fun k t => (e k).symm t) hesymm
  -- `G` is a two-sided inverse of `F`
  have hGF : ∀ (V : S.Opens) (hV : V ≤ T) (s : Γ(M, V)), G V hV (F V hV s) = s := by
    intro V hV s
    refine sections_eq_of_basis M hb hV _ _ fun k hk => ?_
    rw [hGres V hV _ k hk, hFres V hV s k hk, (e k).symm_apply_apply]
  have hFG : ∀ (V : S.Opens) (hV : V ≤ T) (t : Γ(N, V)), F V hV (G V hV t) = t := by
    intro V hV t
    refine sections_eq_of_basis N hb hV _ _ fun k hk => ?_
    rw [hFres V hV _ k hk, hGres V hV t k hk, (e k).apply_symm_apply]
  -- naturality of `F`
  have hFnat : ∀ (V V' : S.Opens) (hV : V ≤ T) (hV' : V' ≤ T) (h : V' ≤ V) (s : Γ(M, V)),
      F V' hV' (M.presheaf.map (homOfLE h).op s) =
        N.presheaf.map (homOfLE h).op (F V hV s) := by
    intro V V' hV hV' h s
    refine sections_eq_of_basis N hb hV' _ _ fun k hk => ?_
    rw [hFres V' hV' _ k hk,
      res_comp N (homOfLE hk) (homOfLE h) (homOfLE (hk.trans h)),
      hFres V hV s k (hk.trans h),
      res_comp M (homOfLE hk) (homOfLE h) (homOfLE (hk.trans h))]
  -- `F` is additive and linear
  have hFadd : ∀ (V : S.Opens) (hV : V ≤ T) (s t : Γ(M, V)),
      F V hV (s + t) = F V hV s + F V hV t := by
    intro V hV s t
    refine sections_eq_of_basis N hb hV _ _ fun k hk => ?_
    rw [hFres V hV _ k hk, map_add, map_add, map_add, hFres V hV s k hk, hFres V hV t k hk]
  have hFsmul : ∀ (V : S.Opens) (hV : V ≤ T) (a : Γ(S, V)) (s : Γ(M, V)),
      F V hV (a • s) = a • F V hV s := by
    intro V hV a s
    refine sections_eq_of_basis N hb hV _ _ fun k hk => ?_
    rw [hFres V hV _ k hk, Scheme.Modules.map_smul, Scheme.Modules.map_smul,
      hFres V hV s k hk, map_smul]
  refine ⟨fun V hV => LinearEquiv.ofBijective
    { toFun := F V hV, map_add' := hFadd V hV, map_smul' := hFsmul V hV }
    ⟨Function.LeftInverse.injective (hGF V hV), Function.RightInverse.surjective (hFG V hV)⟩,
    hFnat, ?_⟩
  intro k hk s
  change F (W k) hk s = e k s
  refine sections_eq_of_basis N hb hk _ _ fun l hl => ?_
  rw [hFres (W k) hk s l hl, he k l hl s]

end

end Stacks.Modules

end

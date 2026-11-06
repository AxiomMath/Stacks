module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Capture
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf

/-!
# Extending a finite type sheaf of ideals from a quasi-compact open, below a given one

Let `Y` be a quasi-compact and quasi-separated scheme, `K` a quasi-coherent sheaf of ideals on
`Y`, `U ⊆ Y` a quasi-compact open and `D` a finite type sheaf of ideals on `U` contained in
`K|_U`.  Then there is a finite type sheaf of ideals `J ⊆ K` on `Y` whose restriction to `U`
is exactly `D`.  In terms of closed subschemes: a closed subscheme of finite presentation of
`U` containing `V(K) ∩ U` extends to a closed subscheme of finite presentation of `Y`
containing `V(K)`.

This is the extension step of Properties, Tag 01PF read at a sheaf of ideals, with the extra
constraint that the extension stays below a prescribed quasi-coherent sheaf of ideals.  It is the
scheme input of the finite presentation approximation of closed subspaces of a quasi-compact
quasi-separated algebraic space, through which Stacks 0860 reaches the second centre of
Stacks 085N.

## Main results

* `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_comap_eq`: the extension.

## Implementation notes

The extension is captured inside `K ⊓ D.map U.ι`: its restriction to `U` lies below
`(D.map U.ι).comap U.ι ≤ D` by the Galois connection, which gives the upper bound for free,
and the generators of `D` over a finite affine cover of `U` lie in it, which the capture lemma
`Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_forall_mem` turns into the lower bound.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.FiniteTypeIdealSheaf

variable {Y : Scheme.{u}}

/-- A finite supremum of finite type sheaves of ideals is of finite type. -/
theorem isFiniteType_finset_sup {X : Scheme.{u}} {α : Type*} (s : Finset α)
    (f : α → X.IdealSheafData) (h : ∀ a ∈ s, (f a).IsFiniteType) :
    (s.sup f).IsFiniteType :=
  Finset.sup_induction isFiniteType_bot (fun _ ha _ hb => ha.sup hb) h

/-- A section over the image of an affine open of `U` lies in the pushforward of a sheaf of
ideals `D` on `U` as soon as its transport to `U` lies in `D`. -/
theorem appIso_inv_mem_ideal_map (U : Y.Opens) [QuasiCompact U.ι]
    (D : U.toScheme.IdealSheafData) (A : U.toScheme.affineOpens) (g : Γ(U.toScheme, A.1))
    (hg : g ∈ D.ideal A) :
    (U.ι.appIso A.1).inv.hom g ∈
      (D.map U.ι).ideal ⟨U.ι ''ᵁ A.1, A.2.image_of_isOpenImmersion U.ι⟩ := by
  have hA : IsAffineOpen (U.ι ⁻¹ᵁ (U.ι ''ᵁ A.1)) := by
    rw [Scheme.Hom.preimage_image_eq]
    exact A.2
  rw [Scheme.IdealSheafData.ideal_map D U.ι _ hA, Ideal.mem_comap,
    ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_app]
  have hle : (⟨U.ι ⁻¹ᵁ (U.ι ''ᵁ A.1), hA⟩ : U.toScheme.affineOpens) ≤ A := by
    show U.ι ⁻¹ᵁ (U.ι ''ᵁ A.1) ≤ A.1
    rw [Scheme.Hom.preimage_image_eq]
  convert Ideal.mem_comap.mp (D.ideal_le_comap_ideal hle hg) using 3
  exact congrArg (fun h => U.toScheme.presheaf.map (Quiver.Hom.op h)) (Subsingleton.elim _ _)

/-- On a compact scheme, an ideal sheaf contained affine-locally in the pullback of `F A` lies in
the pullback of a finite supremum of the `F A`. -/
private theorem exists_finset_le_comap_sup {X Z : Scheme.{u}} [CompactSpace X] (φ : X ⟶ Z)
    (I : X.IdealSheafData) (F : X.affineOpens → Z.IdealSheafData)
    (h : ∀ A, I.ideal A ≤ ((F A).comap φ).ideal A) :
    ∃ σ : Finset X.affineOpens, I ≤ (σ.sup F).comap φ := by
  obtain ⟨σ, hσ⟩ := (IsOpenCover.mk (iSup_affineOpens_eq_top X)).exists_finite_of_compactSpace
  refine ⟨σ, Scheme.IdealSheafData.le_of_iSup_eq_top (fun A : σ => (A.1 : X.affineOpens))
    hσ.iSup_eq_top fun A => (h A.1).trans ?_⟩
  exact Scheme.IdealSheafData.comap_mono φ (Finset.le_sup (f := F) A.2) _

/-- **Extension of a finite type sheaf of ideals from a quasi-compact open, below a given
sheaf of ideals.**  On a quasi-compact quasi-separated scheme `Y`, let `K` be a sheaf of ideals,
`U` a quasi-compact open and `D` a finite type sheaf of ideals on `U` with `D ≤ K|_U`.  Then
some finite type sheaf of ideals `J ≤ K` on `Y` restricts to exactly `D` on `U`. -/
theorem exists_isFiniteType_le_comap_eq [CompactSpace Y] [QuasiSeparatedSpace Y]
    (K : Y.IdealSheafData) (U : Y.Opens) (hU : IsCompact (U : Set Y))
    (D : U.toScheme.IdealSheafData) (hD : D.IsFiniteType) (hDK : D ≤ K.comap U.ι) :
    ∃ J : Y.IdealSheafData, J.IsFiniteType ∧ J ≤ K ∧ J.comap U.ι = D := by
  classical
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact U.ι := (quasiCompact_iff_compactSpace U.ι).mpr inferInstance
  set L := K ⊓ D.map U.ι
  let W : U.toScheme.affineOpens → Y.affineOpens := fun A =>
    ⟨U.ι ''ᵁ A.1, A.2.image_of_isOpenImmersion U.ι⟩
  have key : ∀ A : U.toScheme.affineOpens, ∃ J : Y.IdealSheafData, J.IsFiniteType ∧ J ≤ L ∧
      ∀ g ∈ (hD A).choose, (U.ι.appIso A.1).inv.hom g ∈ J.ideal (W A) := by
    intro A
    obtain ⟨J, hJ, hJL, hJs⟩ := exists_isFiniteType_le_forall_mem L (W A)
      ((hD A).choose.image (U.ι.appIso A.1).inv.hom) (by
        intro x hx
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
        have hgD : g ∈ D.ideal A := (hD A).choose_spec ▸ Ideal.subset_span hg
        refine ⟨?_, appIso_inv_mem_ideal_map U D A g hgD⟩
        have h1 := hDK A hgD
        rwa [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h1)
    exact ⟨J, hJ, hJL, fun g hg => hJs _ (Finset.mem_image_of_mem _ hg)⟩
  choose Jf hJf using key
  obtain ⟨σ, hσ⟩ := exists_finset_le_comap_sup U.ι D Jf fun A => by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, ← (hD A).choose_spec,
      Ideal.span_le]
    exact fun g hg => (hJf A).2.2 g hg
  have hJL : σ.sup Jf ≤ L := Finset.sup_le fun A _ => (hJf A).2.1
  refine ⟨σ.sup Jf, isFiniteType_finset_sup σ Jf fun A _ => (hJf A).1, hJL.trans inf_le_left,
    le_antisymm ?_ hσ⟩
  calc (σ.sup Jf).comap U.ι ≤ (D.map U.ι).comap U.ι :=
        Scheme.IdealSheafData.comap_mono U.ι (hJL.trans inf_le_right)
    _ ≤ D := Scheme.IdealSheafData.comap_map_le _ _

/-- **A finite type sheaf of ideals below a pulled back sheaf of ideals is captured by a finite
type one.**  Let `φ : T ⟶ Y` be a morphism from a quasi-compact scheme to a quasi-compact
quasi-separated scheme, `K` a sheaf of ideals on `Y` and `J ≤ φ⁻¹K` a finite type sheaf of
ideals on `T`.  Then some finite type sheaf of ideals `J₀ ≤ K` on `Y` already has `J ≤ φ⁻¹J₀`.

`K` is the directed supremum of the finite type sheaves of ideals below it
(`Stacks.FiniteTypeIdealSheaf.iSup_isFiniteType_eq`, Properties, Tag 01PG), the inverse image
preserves suprema, and a finitely generated ideal below a supremum lies below a finite part of
it; a finite affine cover of `T` finishes the argument. -/
theorem exists_isFiniteType_le_of_le_comap {T : Scheme.{u}} [CompactSpace T] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (φ : T ⟶ Y) (K : Y.IdealSheafData) (J : T.IdealSheafData)
    (hJ : J.IsFiniteType) (hJK : J ≤ K.comap φ) :
    ∃ J₀ : Y.IdealSheafData, J₀.IsFiniteType ∧ J₀ ≤ K ∧ J ≤ J₀.comap φ := by
  classical
  let ι := {J' : Y.IdealSheafData // J'.IsFiniteType ∧ J' ≤ K}
  have hc : K.comap φ = ⨆ s : ι, s.1.comap φ := by
    conv_lhs => rw [← iSup_isFiniteType_eq K]
    exact (Scheme.IdealSheafData.map_gc φ).l_iSup
  have hsup : ∀ t : Finset ι, (t.sup (fun s : ι => s.1)).IsFiniteType ∧
      t.sup (fun s : ι => s.1) ≤ K := fun t =>
    ⟨isFiniteType_finset_sup t _ fun s _ => s.2.1, Finset.sup_le fun s _ => s.2.2⟩
  have key : ∀ U : T.affineOpens, ∃ t : Finset ι,
      J.ideal U ≤ ((t.sup fun s : ι => s.1).comap φ).ideal U := by
    intro U
    have h1 : J.ideal U ≤ ⨆ s : ι, (s.1.comap φ).ideal U := by
      simpa only [hc, Scheme.IdealSheafData.ideal_iSup, iSup_apply] using hJK U
    obtain ⟨t, ht⟩ := IsCompactElement.exists_finset_of_le_iSup
      ((Submodule.fg_iff_compact _).mp (hJ U)) _ h1
    refine ⟨t, ht.trans (iSup₂_le fun s hs => ?_)⟩
    exact Scheme.IdealSheafData.comap_mono φ (Finset.le_sup (f := fun s : ι => s.1) hs) U
  choose t ht using key
  obtain ⟨σ, hσ⟩ := exists_finset_le_comap_sup φ J (fun U => (t U).sup fun s : ι => s.1) ht
  exact ⟨σ.sup fun U => (t U).sup fun s : ι => s.1,
    isFiniteType_finset_sup σ _ fun U _ => (hsup (t U)).1,
    Finset.sup_le fun U _ => (hsup (t U)).2, hσ⟩

end Stacks.FiniteTypeIdealSheaf

end

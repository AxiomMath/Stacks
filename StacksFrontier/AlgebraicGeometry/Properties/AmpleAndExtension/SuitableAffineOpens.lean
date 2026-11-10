module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# A separated dense open subscheme of a quasi-compact scheme

Every quasi-compact scheme has a dense open subscheme which is separated. The subscheme is built
by induction on a finite affine cover: a finite coproduct of separated schemes is separated, and
a disjoint union of separated opens is separated, so one may take the union of the mutually
disjoint "new" parts of the members of the cover.

## Main results

* `AlgebraicGeometry.exists_dense_open_isSeparated`: a quasi-compact scheme has a dense
  separated open subscheme.

## Implementation notes

Quasi-compactness of a scheme is the `CompactSpace` instance on its underlying space. An open
subset carries its canonical open subscheme structure, so `Scheme.IsSeparated V` says that this
open subscheme is separated.

## References

* [Stacks Project, Tag 03J1](https://stacks.math.columbia.edu/tag/03J1)
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme with a separated morphism to a separated scheme is separated. -/
private theorem isSeparated_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [Scheme.IsSeparated Y] : Scheme.IsSeparated X :=
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

private theorem isSeparated_coprod {X Y : Scheme.{u}} [Scheme.IsSeparated X]
    [Scheme.IsSeparated Y] : Scheme.IsSeparated (X ⨿ Y) := by
  let fX : X ⟶ (⊤_ Scheme.{u}) := terminal.from X
  let fY : Y ⟶ (⊤_ Scheme.{u}) := terminal.from Y
  let codiag : (⊤_ Scheme.{u}) ⨿ (⊤_ Scheme.{u}) ⟶ (⊤_ Scheme.{u}) :=
    coprod.desc (𝟙 _) (𝟙 _)
  have hcodiag : IsSeparated codiag := IsSeparated.of_isAffineHom codiag
  have hmap : IsSeparated (coprod.map fX fY) :=
    IsZariskiLocalAtTarget.coprodMap fX fY inferInstance inferInstance
  exact isSeparated_of_hom (coprod.map fX fY ≫ codiag)

private theorem isSeparated_open_sup_of_disjoint {X : Scheme.{u}} (U V : X.Opens)
    (hUV : Disjoint U V) (hU : Scheme.IsSeparated U) (hV : Scheme.IsSeparated V) :
    Scheme.IsSeparated ((U ⊔ V : X.Opens).toScheme) := by
  let S : X.Opens := U ⊔ V
  let f : U.toScheme ⟶ S.toScheme := X.homOfLE le_sup_left
  let g : V.toScheme ⟶ S.toScheme := X.homOfLE le_sup_right
  let : IsOpenImmersion f := inferInstance
  let : IsOpenImmersion g := inferInstance
  have hcompl : IsCompl f.opensRange g.opensRange := by
    rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, isCompl_iff]
    constructor
    · rw [disjoint_iff] at hUV
      rw [disjoint_iff, ← Scheme.Hom.preimage_inf, hUV, Scheme.Hom.preimage_bot]
    · rw [codisjoint_iff_le_sup, ← Scheme.Hom.preimage_sup]
      simp [S]
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl f g hcompl
  let e : U.toScheme ⨿ V.toScheme ≅ S.toScheme :=
    (coprodIsCoprod _ _).coconePointUniqueUpToIso hc
  let : Scheme.IsSeparated (U.toScheme ⨿ V.toScheme) := isSeparated_coprod
  exact isSeparated_of_hom e.inv

private theorem isSeparated_of_affine_open_superset {X : Scheme.{u}}
    (U V : X.Opens) (hUV : U ≤ V) (hV : IsAffineOpen V) : Scheme.IsSeparated U := by
  let : IsAffine V.toScheme := hV
  let f : U.toScheme ⟶ V.toScheme := X.homOfLE hUV
  exact isSeparated_of_hom f

private theorem exists_separated_open_dense_in_iSup {X : Scheme.{u}} :
    ∀ n (U : Fin n → X.Opens), (∀ i, IsAffineOpen (U i)) →
      ∃ V : X.Opens, V ≤ ⨆ i, U i ∧
        ((⨆ i, U i : X.Opens) : Set X) ⊆ closure (V : Set X) ∧ Scheme.IsSeparated V := by
  intro n
  induction n with
  | zero =>
      intro U hU
      refine ⟨⊥, bot_le, by simp, ?_⟩
      let : IsAffine (⊥ : X.Opens).toScheme := isAffineOpen_bot X
      infer_instance
  | succ n ih =>
      intro U hU
      let T : X.Opens := ⨆ i : Fin n, U i.castSucc
      obtain ⟨V', hV'le, hTdense, hV'sep⟩ := ih (fun i => U i.castSucc)
        (fun i => hU i.castSucc)
      let C : X.Opens := ⟨(closure (V' : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
      let W : X.Opens := U (Fin.last n) ⊓ C
      let V : X.Opens := V' ⊔ W
      have hdisj : Disjoint V' W := by
        rw [disjoint_iff]
        ext x
        change (x ∈ V' ∧ x ∈ W) ↔ x ∈ (⊥ : X.Opens)
        constructor
        · rintro ⟨hxV, hxW⟩
          have hxW' : x ∈ U (Fin.last n) ∧ x ∉ closure (V' : Set X) := by
            simpa [W, C] using hxW
          exact False.elim (hxW'.2 (subset_closure hxV))
        · simp
      have hWsep : Scheme.IsSeparated W :=
        isSeparated_of_affine_open_superset W (U (Fin.last n)) inf_le_left
          (hU (Fin.last n))
      have hVsep : Scheme.IsSeparated V :=
        isSeparated_open_sup_of_disjoint V' W hdisj hV'sep hWsep
      have hV'V : closure (V' : Set X) ⊆ closure (V : Set X) :=
        closure_mono fun _ hx => Or.inl hx
      have hUcl : (U (Fin.last n) : Set X) ⊆ closure (V : Set X) := by
        intro x hx
        by_cases h : x ∈ closure (V' : Set X)
        · exact hV'V h
        · have hxW : x ∈ W := by
            change x ∈ U (Fin.last n) ∧ x ∈ C
            exact ⟨hx, by simpa [C] using h⟩
          exact subset_closure (Or.inr hxW)
      have hsplit : (⨆ i : Fin (n + 1), U i) = T ⊔ U (Fin.last n) := by
        refine le_antisymm (iSup_le fun i => Fin.lastCases ?_ (fun j => ?_) i)
          (sup_le (iSup_le fun i => le_iSup U i.castSucc) (le_iSup U (Fin.last n)))
        · exact le_sup_right
        · exact le_sup_of_le_left (le_iSup (fun j : Fin n => U j.castSucc) j)
      rw [hsplit]
      exact ⟨V, sup_le (hV'le.trans le_sup_left) (inf_le_left.trans le_sup_right),
        Set.union_subset (hTdense.trans hV'V) hUcl, hVsep⟩

/-- A quasi-compact scheme has a separated dense open subscheme. -/
@[stacks 03J1, sga "3 VIB 5.8.3" "special case"]
theorem exists_dense_open_isSeparated (X : Scheme.{u}) [CompactSpace X] :
    ∃ V : X.Opens, Dense (V : Set X) ∧ Scheme.IsSeparated V := by
  let : ∀ i, IsAffine ((X.affineOpenCover.openCover).X i) :=
    fun i ↦ Scheme.isAffine_affineOpenCover X X.affineOpenCover i
  let 𝒰 := X.affineOpenCover.openCover.finiteSubcover
  let n := Fintype.card 𝒰.I₀
  let e : Fin n ≃ 𝒰.I₀ := (Fintype.equivFin 𝒰.I₀).symm
  let U : Fin n → X.Opens := fun i ↦ (𝒰.f (e i)).opensRange
  have hcover : (⨆ i : Fin n, U i) = ⊤ := by
    simpa [U] using (e.iSup_comp (g := fun j : 𝒰.I₀ ↦ (𝒰.f j).opensRange)).trans
      𝒰.iSup_opensRange
  obtain ⟨V, -, hVdense, hVsep⟩ := exists_separated_open_dense_in_iSup n U
    (fun i ↦ isAffineOpen_opensRange (𝒰.f (e i)))
  refine ⟨V, ?_, hVsep⟩
  intro x
  exact hVdense (by simp [hcover])

end AlgebraicGeometry

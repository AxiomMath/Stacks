module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolution
public import StacksFrontier.CategoryTheory.Triangulated.PostnikovSystems
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts

/-!
# The brutal truncations of a complex: triangles and derived colimit

Let `L` be a cochain complex in an abelian category `A`, read as the chain complex
`… → L₂ → L₁ → L₀` with `Lₙ = L⁻ⁿ`. Put `Xₙ = Lₙ` in `D(A)` and let `Yₙ` be the brutal
truncation `σ^{≥-n}L = (Lₙ → … → L₀)` shifted into cohomological degrees `0, …, n`. The brutal
truncations sit in short exact sequences `0 → σ^{≥p+1}L → σ^{≥p}L → Lᵖ[p] → 0` which are split
in every degree, so after shifting by `p` and rotating one obtains, for `p = -n-1`, a
distinguished triangle `Yₙ₊₁ → Xₙ₊₁ → Yₙ → Yₙ₊₁[1]` whose first map is the projection of the
truncation onto its bottom term. In the other direction `L` is the ordinary colimit of its
brutal truncations, because in each degree that tower is eventually constant, and a termwise
colimit of complexes computes the derived colimit when colimits over `ℕ` are exact; hence
`L = hocolim Yₙ[n]`.

Applied to the resolution `… → g₂!ℤ → g₁!ℤ → g₀!ℤ` of the constant sheaf `ℤ` on the total site
of a simplicial-site situation, this produces the triangles and the derived colimit attached to
the integral resolution, and both statements persist under any exact functor of `D(𝒞_total)`
commuting with countable direct sums, such as `- ⊗^L_ℤ K` for an object `K`.

## Main definitions

* `StacksDraft.BrutalPostnikov.term` and `.tot`: the objects `Xₙ` and `Yₙ`.
* `StacksDraft.BrutalPostnikov.totProj` and `.termToTotAt`: the canonical maps `Yₙ ⟶ Xₙ` and
  `Xₙ₊₁ ⟶ Yₙ`.
* `StacksDraft.BrutalPostnikov.truncTower`: the tower `n ↦ σ^{≥-n}L`, i.e. `n ↦ Yₙ[n]`.
* `StacksDraft.BrutalPostnikov.truncTriangleAt`: the triangle `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]`.
* `StacksDraft.BrutalPostnikov.postnikovSystem`: the Postnikov system those triangles form for
  the length-`N` truncation `X_N ⟶ ⋯ ⟶ X₁ ⟶ X₀` of the complex of terms of `L`.
* `CategoryTheory.SimplicialSiteSituation.integerResolutionComplex`: the resolution of Stacks
  09WI as a cochain complex supported in degrees `≤ 0`.

## Main results

* `StacksDraft.BrutalPostnikov.isColimitTruncTowerCocone`: a complex is the colimit of its
  brutal truncations.
* `StacksDraft.BrutalPostnikov.truncTriangleAt_distinguished`: the triangle
  `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` is distinguished.
* `StacksDraft.BrutalPostnikov.termToTotHom_comp_totProjHom`: the composite
  `Xₙ₊₁ ⟶ Yₙ ⟶ Xₙ` is the differential of the complex, up to the sign `(-1)ᵃ`.
* `StacksDraft.BrutalPostnikov.isHomotopyColimit_truncTower`: `L = hocolim Yₙ[n]`.

## References

* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D8Z](https://stacks.math.columbia.edu/tag/0D8Z)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open ComplexShape HomologicalComplex
open scoped Simplicial
open StacksDraft.StupidTruncation

namespace StacksDraft.BrutalPostnikov

universe w v u

/-! ### A complex is the colimit of its brutal truncations -/

section Tower

variable {A : Type u} [Category.{v} A] [Abelian A] (L : CochainComplex A ℤ)

/-- The tower `n ↦ σ^{≥-n}L` of brutal truncations of `L`, that is `n ↦ Yₙ[n]`, with the
inclusions of one truncation into the next as transition maps. -/
def truncTower : ℕ ⥤ CochainComplex A ℤ where
  obj n := L.stupidTrunc (embeddingUpIntGE (-(n : ℤ)))
  map {m n} f := stupidTruncGEMapLE L (neg_le_neg (Int.ofNat_le.2 (leOfHom f)))
  map_id := fun n => by
    have := mono_ιStupidTrunc L (embeddingUpIntGE (-(n : ℤ)))
    apply (cancel_mono (ιStupidTrunc L (embeddingUpIntGE (-(n : ℤ))))).1
    rw [stupidTruncGEMapLE_ι, Category.id_comp]
  map_comp := fun {_ _ k} f g => by
    have := mono_ιStupidTrunc L (embeddingUpIntGE (-(k : ℤ)))
    apply (cancel_mono (ιStupidTrunc L (embeddingUpIntGE (-(k : ℤ))))).1
    rw [Category.assoc, stupidTruncGEMapLE_ι, stupidTruncGEMapLE_ι, stupidTruncGEMapLE_ι]

/-- The cocone on the tower of brutal truncations with vertex `L`, given by the inclusions
`σ^{≥-n}L ⟶ L`. -/
def truncTowerCocone : Cocone (truncTower L) where
  pt := L
  ι :=
    { app := fun n => ιStupidTrunc L (embeddingUpIntGE (-(n : ℤ)))
      naturality := fun _ _ f =>
        (stupidTruncGEMapLE_ι L (neg_le_neg (Int.ofNat_le.2 (leOfHom f)))).trans
          (Category.comp_id _).symm }

/-- A complex is the colimit of the tower of its brutal truncations, by the inclusions
`σ^{≥-n}L ⟶ L`. -/
def isColimitTruncTowerCocone : IsColimit (truncTowerCocone L) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun i => ?_
  have hc : Functor.IsEventuallyConstantFrom
      (truncTower L ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) (-i).toNat := by
    intro j f
    have hj : ((-i).toNat : ℤ) ≤ (j : ℤ) := Int.ofNat_le.2 (leOfHom f)
    have h : IsIso ((stupidTruncGEMapLE L
        (neg_le_neg (Int.ofNat_le.2 (leOfHom f)) : -(j : ℤ) ≤ -(((-i).toNat : ℕ) : ℤ))).f i) := by
      rw [stupidTruncGEMapLE_f L _ i (by omega)]
      infer_instance
    exact h
  haveI : IsIso (((HomologicalComplex.eval A (ComplexShape.up ℤ) i).mapCocone
      (truncTowerCocone L)).ι.app (-i).toNat) := by
    have h : IsIso ((ιStupidTrunc L (embeddingUpIntGE (-(((-i).toNat : ℕ) : ℤ)))).f i) := by
      rw [ιStupidTruncGE_f L _ i (by omega)]
      infer_instance
    exact h
  exact hc.isColimitOfIsIso _

/-- The tower of brutal truncations of `L` has a colimit. -/
instance : HasColimit (truncTower L) :=
  ⟨_, isColimitTruncTowerCocone L⟩

/-- The identification of the colimit of the tower of brutal truncations with `L`. -/
def colimitTruncTowerIso : colimit (truncTower L) ≅ L :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitTruncTowerCocone L)

end Tower

/-! ### The brutal-truncation sequence and its splittings -/

section Splitting

variable {A : Type u} [Category.{v} A] [Abelian A] (L : CochainComplex A ℤ)

/-- The brutal-truncation sequence `0 ⟶ σ^{≥p+1}L ⟶ σ^{≥p}L ⟶ (single p).obj Lᵖ ⟶ 0` is split
in every degree: in degree `p` its first term vanishes and its second map is invertible, in
every other degree its first map is invertible and its last term vanishes. -/
def truncSplitting (p n : ℤ) :
    ((stupidTruncGEShortComplex L p).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).Splitting := by
  by_cases hn : n = p
  · subst hn
    refine ShortComplex.Splitting.ofIsZeroOfIsIso _
      (CochainComplex.isZero_of_isStrictlyGE
        (L.stupidTrunc (embeddingUpIntGE (n + 1))) (n + 1) n (by omega)) ?_
    have h : IsIso ((stupidTruncGEπ L n).f n) := by
      rw [stupidTruncGEπ_f]
      infer_instance
    exact h
  · refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_
      (isZero_single_obj_X (ComplexShape.up ℤ) p (L.X p) n hn)
    rcases lt_or_ge p n with hpn | hpn
    · have h : IsIso ((stupidTruncGEMapLE L (show p ≤ p + 1 by omega)).f n) := by
        rw [stupidTruncGEMapLE_f L _ n (by omega)]
        infer_instance
      exact h
    · exact IsZero.isIso
        (CochainComplex.isZero_of_isStrictlyGE
          (L.stupidTrunc (embeddingUpIntGE (p + 1))) (p + 1) n (by omega))
        (CochainComplex.isZero_of_isStrictlyGE
          (L.stupidTrunc (embeddingUpIntGE p)) p n (by omega)) _

/-- The brutal-truncation sequence at `p`, shifted by `p`, so that its last term is `Lᵖ` placed
in cohomological degree zero. -/
def shiftedTruncShortComplex (p : ℤ) : ShortComplex (CochainComplex A ℤ) :=
  (stupidTruncGEShortComplex L p).map (CategoryTheory.shiftFunctor (CochainComplex A ℤ) p)

/-- The shifted brutal-truncation sequence is split in every degree: its degree-`n` component
is the degree-`n + p` component of the unshifted sequence. -/
def shiftedTruncSplitting (p n : ℤ) :
    ((shiftedTruncShortComplex L p).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).Splitting :=
  truncSplitting L p (n + p)

/-- The component of the projection `σ^{≥p}L ⟶ Lᵖ[p]` in a degree presented as an expression
equal to `p`: it is the identification of the term of the truncation with `Lᵖ`. -/
private lemma stupidTruncGEπ_f_of_eq (p n : ℤ) (h : n = p) :
    (stupidTruncGEπ L p).f n = (stupidTruncGEXIso L p n (by omega)).hom ≫
      (L.XIsoOfEq h).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p (L.X p)).inv ≫
      (((HomologicalComplex.single A (ComplexShape.up ℤ) p).obj (L.X p)).XIsoOfEq h).inv := by
  subst h
  simpa using stupidTruncGEπ_f L _

/-- Between two retained degrees the differential of a brutal truncation is the differential of
`L`, read through the identifications of the terms. -/
private lemma stupidTruncGE_d_eq (b m n : ℤ) (hm : b ≤ m) (hn : b ≤ n) :
    (L.stupidTrunc (embeddingUpIntGE b)).d m n =
      (stupidTruncGEXIso L b m hm).hom ≫ L.d m n ≫ (stupidTruncGEXIso L b n hn).inv := by
  have h := (ιStupidTrunc L (embeddingUpIntGE b)).comm m n
  rw [ιStupidTruncGE_f L b m hm, ιStupidTruncGE_f L b n hn] at h
  exact ((Iso.eq_comp_inv _).2 h.symm).trans (Category.assoc _ _ _)

/-- A differential of `L` read at degrees presented as expressions equal to the intended ones. -/
private lemma d_of_eq (m n m' n' : ℤ) (hm : m = m') (hn : n = n') :
    L.d m n = (L.XIsoOfEq hm).hom ≫ L.d m' n' ≫ (L.XIsoOfEq hn).inv := by
  subst hm
  subst hn
  simp

/-- The degree-`n` component of the connecting morphism of the shifted brutal-truncation
sequence: the section of its projection, the differential, and the retraction of its
inclusion. -/
private lemma homOfDegreewiseSplit_shiftedTrunc_f (a n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit (shiftedTruncShortComplex L a)
        (shiftedTruncSplitting L a)).f n =
      (shiftedTruncSplitting L a n).s ≫
        (shiftedTruncShortComplex L a).X₂.d n (n + 1) ≫
        (shiftedTruncSplitting L a (n + 1)).r := by
  rw [CochainComplex.homOfDegreewiseSplit_f]
  rfl

end Splitting

/-! ### Transport of a homotopy colimit along an isomorphism -/

section Transport

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Being a derived colimit of a system is invariant under isomorphism of the target. -/
theorem isHomotopyColimit_of_iso {F : ℕ ⥤ D} [HasCoproduct F.obj] {K K' : D}
    (h : IsHomotopyColimit F K) (e : K ≅ K') : IsHomotopyColimit F K' := by
  obtain ⟨p, q, hT⟩ := h
  refine ⟨p ≫ e.hom, e.inv ≫ q, isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_)⟩
  · simp
  · simp
  · simp

/-- An isomorphism scaled by a sign is again an isomorphism. -/
private def unitsSmulIso {X Y : D} (u : ℤˣ) (e : X ≅ Y) : X ≅ Y where
  hom := u • e.hom
  inv := u • e.inv
  hom_inv_id := by simp [Units.smul_def, smul_smul]
  inv_hom_id := by simp [Units.smul_def, smul_smul]

end Transport

/-! ### The triangle of a degreewise split sequence in the derived category -/

section Degreewise

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The triangle attached to a degreewise split short exact sequence of cochain complexes is
distinguished in the derived category. -/
theorem distinguished_mapTriangle_degreewiseSplit (S : ShortComplex (CochainComplex A ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).Splitting) :
    DerivedCategory.Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S σ) ∈
      distTriang (DerivedCategory A) :=
  isomorphic_distinguished _ (DerivedCategory.Qh.map_distinguished _
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ)) _
    ((Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso A)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        DerivedCategory.Qh).app _)

end Degreewise

/-! ### The two families of objects, and the canonical projection -/

section Objects

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (L : CochainComplex A ℤ)

/-- The identification `(M[a])[a] ≅ M[0]` of cochain complexes: an object placed in
cohomological degree `a` and then shifted by `a` sits in degree zero. -/
abbrev singleShiftIso (a : ℤ) (M : A) :
    ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj M)⟦a⟧ ≅
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M :=
  ((CochainComplex.singleFunctors A).shiftIso a 0 a (by simp)).app M

/-- The term `Lᵃ` of the complex, as an object of `D(A)` concentrated in degree zero; for
`a = -n` this is `Xₙ = Lₙ`. -/
def termAt (a : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj (L.X a)

/-- The brutal truncation `σ^{≥a}L` shifted by `a`, as an object of `D(A)`; for `a = -n` this
is `Yₙ = (Lₙ → … → L₀)[-n]`, whose terms sit in cohomological degrees `0, …, n`. -/
def totAt (a : ℤ) : DerivedCategory A :=
  DerivedCategory.Q.obj ((L.stupidTrunc (embeddingUpIntGE a))⟦a⟧)

/-- The term `Xₙ = Lₙ = L⁻ⁿ` of the complex, as an object of `D(A)` concentrated in degree
zero. -/
def term (n : ℕ) : DerivedCategory A :=
  termAt L (-(n : ℤ))

/-- The object `Yₙ = (Lₙ → … → L₀)[-n]`: the brutal truncation `σ^{≥-n}L` of `L`, shifted so
that its terms sit in cohomological degrees `0, …, n`. -/
def tot (n : ℕ) : DerivedCategory A :=
  totAt L (-(n : ℤ))

/-- The projection of a brutal truncation onto its bottom term, shifted into degree zero, at
the level of complexes. -/
def totProjHom (a : ℤ) :
    (L.stupidTrunc (embeddingUpIntGE a))⟦a⟧ ⟶
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (L.X a) :=
  (stupidTruncGEπ L a)⟦a⟧' ≫ (singleShiftIso a (L.X a)).hom

/-- The canonical map `Yₙ ⟶ Xₙ`: the projection of the brutal truncation onto its bottom
term, shifted into degree zero. -/
def totProjAt (a : ℤ) : totAt L a ⟶ termAt L a :=
  DerivedCategory.Q.map (totProjHom L a)

/-- The canonical map `Yₙ ⟶ Xₙ`. -/
def totProj (n : ℕ) : tot L n ⟶ term L n :=
  totProjAt L (-(n : ℤ))

/-- The canonical map `Xₙ₊₁ ⟶ Yₙ` at the level of complexes: the connecting morphism of the
degreewise split brutal-truncation sequence, with its two shifts rearranged. -/
def termToTotHom (a : ℤ) :
    (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (L.X a) ⟶
      (L.stupidTrunc (embeddingUpIntGE (a + 1)))⟦a + 1⟧ :=
  ((singleShiftIso a (L.X a)).inv ≫
      CochainComplex.homOfDegreewiseSplit _ (shiftedTruncSplitting L a)) ≫
    ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).app
      (L.stupidTrunc (embeddingUpIntGE (a + 1)))).inv

/-- The canonical map `Xₙ₊₁ ⟶ Yₙ`. -/
def termToTotAt (a : ℤ) : termAt L a ⟶ totAt L (a + 1) :=
  DerivedCategory.Q.map (termToTotHom L a)

/-- The identification of `Yₙ₊₁` with the shift by `1` of the brutal truncation `σ^{≥a+1}L`
shifted by `a`. -/
abbrev totShiftIso (a : ℤ) :
    totAt L (a + 1) ≅
      (DerivedCategory.Q.obj ((L.stupidTrunc (embeddingUpIntGE (a + 1)))⟦a⟧))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.mapIso ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).app
      (L.stupidTrunc (embeddingUpIntGE (a + 1)))) ≪≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app
      ((L.stupidTrunc (embeddingUpIntGE (a + 1)))⟦a⟧)

/-- The connecting morphism `Yₙ ⟶ Yₙ₊₁[1]`: the shift of the inclusion of one brutal
truncation into the next, with the sign introduced by the rotation. -/
def totConnectingAt (a : ℤ) : totAt L (a + 1) ⟶ (totAt L a)⟦(1 : ℤ)⟧ :=
  (totShiftIso L a).hom ≫
    (-((DerivedCategory.Q.map
      ((stupidTruncGEMapLE L (show a ≤ a + 1 by omega))⟦a⟧'))⟦(1 : ℤ)⟧'))

omit [HasDerivedCategory.{w} A] in
/-- Composing the canonical map `Xₙ₊₁ ⟶ Yₙ` with the comparison of the two shifts recovers the
connecting morphism of the degreewise split brutal-truncation sequence. -/
private theorem termToTotHom_comp_shiftFunctorAdd' (a : ℤ) :
    termToTotHom L a ≫ ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).app
        (L.stupidTrunc (embeddingUpIntGE (a + 1)))).hom =
      (singleShiftIso a (L.X a)).inv ≫
        CochainComplex.homOfDegreewiseSplit _ (shiftedTruncSplitting L a) :=
  (Iso.eq_comp_inv _).mp rfl

/-- The same identity after passing to the derived category, with each morphism mapped
separately. -/
private theorem Q_termToTotHom_comp_shiftFunctorAdd' (a : ℤ) :
    DerivedCategory.Q.map (termToTotHom L a) ≫
        DerivedCategory.Q.map ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).app
          (L.stupidTrunc (embeddingUpIntGE (a + 1)))).hom =
      DerivedCategory.Q.map (singleShiftIso a (L.X a)).inv ≫
        DerivedCategory.Q.map
          (CochainComplex.homOfDegreewiseSplit _ (shiftedTruncSplitting L a)) := by
  rw [← DerivedCategory.Q.map_comp, termToTotHom_comp_shiftFunctorAdd']
  exact DerivedCategory.Q.map_comp _ _

omit [HasDerivedCategory.{w} A] in
/-- **The composite `Xₙ₊₁ ⟶ Yₙ ⟶ Xₙ` is the differential of the complex, up to the sign
`(-1)ᵃ`.** At the level of complexes, the canonical map `Lᵃ ⟶ σ^{≥a+1}L[a+1]` followed by the
projection of `σ^{≥a+1}L[a+1]` onto its bottom term is `(-1)ᵃ` times the differential
`Lᵃ ⟶ Lᵃ⁺¹`. -/
theorem termToTotHom_comp_totProjHom (a : ℤ) :
    termToTotHom L a ≫ totProjHom L (a + 1) =
      a.negOnePow •
        (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map (L.d a (a + 1)) := by
  have hle : a ≤ a + 1 := by omega
  have h0 : (0 : ℤ) + a = a := by ring
  have h1 : (0 : ℤ) + 1 + a = a + 1 := by ring
  have hk : (0 : ℤ) + (a + 1) = a + 1 := by ring
  have hjk : (0 : ℤ) + 1 + a = 0 + (a + 1) := by ring
  have hia : a ≤ 0 + a := by omega
  have hja : a ≤ 0 + 1 + a := by omega
  have hja1 : a + 1 ≤ 0 + 1 + a := by omega
  have hka1 : a + 1 ≤ 0 + (a + 1) := by omega
  have bridge : ∀ (b m n : ℤ) (hm : b ≤ m) (hn : b ≤ n) (h : m = n) (W : A) (g : L.X n ⟶ W),
      (stupidTruncGEXIso L b m hm).inv ≫
        ((L.stupidTrunc (embeddingUpIntGE b)).XIsoOfEq h).hom ≫
          (stupidTruncGEXIso L b n hn).hom ≫ g = (L.XIsoOfEq h).hom ≫ g := by
    intro b m n hm hn h W g
    subst h
    simp
  have hmono : IsIso ((stupidTruncGEπ L a).f (0 + a)) := by
    rw [stupidTruncGEπ_f_of_eq L a (0 + a) h0]
    infer_instance
  have hepi : IsIso ((stupidTruncGEMapLE L hle).f (0 + 1 + a)) := by
    rw [stupidTruncGEMapLE_f L hle (0 + 1 + a) hja1]
    infer_instance
  have hs : (((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj (L.X a)).XIsoOfEq h0).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (L.X a)).hom ≫
        (L.XIsoOfEq h0).inv ≫ (stupidTruncGEXIso L a (0 + a) hia).inv =
      (shiftedTruncSplitting L a 0).s := by
    have h :
        ((((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj (L.X a)).XIsoOfEq h0).hom ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (L.X a)).hom ≫
            (L.XIsoOfEq h0).inv ≫ (stupidTruncGEXIso L a (0 + a) hia).inv) ≫
          (stupidTruncGEπ L a).f (0 + a) = 𝟙 _ := by
      rw [stupidTruncGEπ_f_of_eq L a (0 + a) h0]
      simp
    exact (cancel_mono ((stupidTruncGEπ L a).f (0 + a))).1
      (h.trans (shiftedTruncSplitting L a 0).s_g.symm)
  have hr : (stupidTruncGEXIso L a (0 + 1 + a) hja).hom ≫
        (stupidTruncGEXIso L (a + 1) (0 + 1 + a) hja1).inv =
      (shiftedTruncSplitting L a (0 + 1)).r := by
    have h : (stupidTruncGEMapLE L hle).f (0 + 1 + a) ≫
        ((stupidTruncGEXIso L a (0 + 1 + a) hja).hom ≫
          (stupidTruncGEXIso L (a + 1) (0 + 1 + a) hja1).inv) = 𝟙 _ := by
      rw [stupidTruncGEMapLE_f L hle (0 + 1 + a) hja1]
      simp
    exact (cancel_epi ((stupidTruncGEMapLE L hle).f (0 + 1 + a))).1
      (h.trans (shiftedTruncSplitting L a (0 + 1)).f_r.symm)
  have hd : (shiftedTruncShortComplex L a).X₂.d 0 (0 + 1) =
      a.negOnePow • (L.stupidTrunc (embeddingUpIntGE a)).d (0 + a) (0 + 1 + a) := rfl
  have final :
      (((singleShiftIso a (L.X a)).inv.f 0 ≫
            ((((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj (L.X a)).XIsoOfEq h0).hom ≫
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (L.X a)).hom ≫
                (L.XIsoOfEq h0).inv ≫ (stupidTruncGEXIso L a (0 + a) hia).inv) ≫
              (a.negOnePow • (L.stupidTrunc (embeddingUpIntGE a)).d (0 + a) (0 + 1 + a)) ≫
                ((stupidTruncGEXIso L a (0 + 1 + a) hja).hom ≫
                  (stupidTruncGEXIso L (a + 1) (0 + 1 + a) hja1).inv)) ≫
          ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).inv.app
            (L.stupidTrunc (embeddingUpIntGE (a + 1)))).f 0) ≫
        ((stupidTruncGEπ L (a + 1)).f (0 + (a + 1)) ≫
          (singleShiftIso (a + 1) (L.X (a + 1))).hom.f 0) =
      (a.negOnePow •
        (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map (L.d a (a + 1))).f 0 := by
    rw [stupidTruncGE_d_eq L a (0 + a) (0 + 1 + a) hia hja,
      d_of_eq L (0 + a) (0 + 1 + a) a (a + 1) h0 h1,
      stupidTruncGEπ_f_of_eq L (a + 1) (0 + (a + 1)) hk,
      CochainComplex.shiftFunctorAdd'_inv_app_f']
    simp only [Category.assoc]
    rw [bridge (a + 1) (0 + 1 + a) (0 + (a + 1)) hja1 hka1 hjk]
    simp [HomologicalComplex.single_map_f_self, singleShiftIso, CochainComplex.singleFunctors,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.XIsoOfEq]
  ext
  change (((singleShiftIso a (L.X a)).inv.f 0 ≫
        (CochainComplex.homOfDegreewiseSplit (shiftedTruncShortComplex L a)
          (shiftedTruncSplitting L a)).f 0) ≫
      (((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).app
        (L.stupidTrunc (embeddingUpIntGE (a + 1)))).inv).f 0) ≫
      ((stupidTruncGEπ L (a + 1)).f (0 + (a + 1)) ≫
        (singleShiftIso (a + 1) (L.X (a + 1))).hom.f 0) = _
  rw [homOfDegreewiseSplit_shiftedTrunc_f, hd, ← hs, ← hr]
  exact final

/-- **The composite `Xₙ₊₁ ⟶ Yₙ ⟶ Xₙ` in `D(A)` is the differential of the complex, up to the
sign `(-1)ᵃ`.** -/
theorem termToTotAt_comp_totProjAt (a : ℤ) :
    termToTotAt L a ≫ totProjAt L (a + 1) =
      a.negOnePow • (DerivedCategory.singleFunctor A 0).map (L.d a (a + 1)) := by
  have h : DerivedCategory.Q.map (termToTotHom L a ≫ totProjHom L (a + 1)) =
      a.negOnePow • (DerivedCategory.singleFunctor A 0).map (L.d a (a + 1)) := by
    rw [termToTotHom_comp_totProjHom, Units.smul_def, Units.smul_def,
      CategoryTheory.Functor.map_zsmul]
    rfl
  exact (DerivedCategory.Q.map_comp _ _).symm.trans h

/-- The same identity with the target degree presented as an expression equal to `a + 1`. -/
private theorem termToTotAt_comp_totProjAt' (a b : ℤ) (h : a + 1 = b) :
    termToTotAt L a ≫ eqToHom (congrArg (totAt L) h) ≫ totProjAt L b =
      a.negOnePow • (DerivedCategory.singleFunctor A 0).map (L.d a b) := by
  subst h
  simpa using termToTotAt_comp_totProjAt L a

/-- **The brutal-truncation triangle** `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]`, written at the index
`a = -n-1`, so that it reads `Yₐ ⟶ Xₐ ⟶ Yₐ₊₁ ⟶ Yₐ[1]`. -/
def truncTriangleAt (a : ℤ) : Triangle (DerivedCategory A) :=
  Triangle.mk (totProjAt L a) (termToTotAt L a) (totConnectingAt L a)

/-- **The triangles `Yₙ ⟶ Xₙ ⟶ Yₙ₋₁ ⟶ Yₙ[1]` are distinguished.** -/
theorem truncTriangleAt_distinguished (a : ℤ) :
    truncTriangleAt L a ∈ distTriang (DerivedCategory A) := by
  have hT : Triangle.mk (DerivedCategory.Q.map (shiftedTruncShortComplex L a).g)
      (DerivedCategory.Q.map
          (CochainComplex.homOfDegreewiseSplit _ (shiftedTruncSplitting L a)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (shiftedTruncShortComplex L a).X₁)
      (-((DerivedCategory.Q.map (shiftedTruncShortComplex L a).f)⟦(1 : ℤ)⟧')) ∈
        distTriang (DerivedCategory A) :=
    rot_of_distTriang _ (distinguished_mapTriangle_degreewiseSplit _ (shiftedTruncSplitting L a))
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _)
    (DerivedCategory.Q.mapIso (singleShiftIso a (L.X a))).symm (totShiftIso L a) ?_ ?_ ?_)
  · change DerivedCategory.Q.map (totProjHom L a) ≫
        DerivedCategory.Q.map (singleShiftIso a (L.X a)).inv =
      𝟙 _ ≫ DerivedCategory.Q.map (shiftedTruncShortComplex L a).g
    rw [Category.id_comp, ← CategoryTheory.Functor.map_comp, totProjHom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    rfl
  · change DerivedCategory.Q.map (termToTotHom L a) ≫
        (DerivedCategory.Q.map ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).app
              (L.stupidTrunc (embeddingUpIntGE (a + 1)))).hom ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            ((L.stupidTrunc (embeddingUpIntGE (a + 1)))⟦a⟧)) =
      DerivedCategory.Q.map (singleShiftIso a (L.X a)).inv ≫
        (DerivedCategory.Q.map
            (CochainComplex.homOfDegreewiseSplit _ (shiftedTruncSplitting L a)) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (shiftedTruncShortComplex L a).X₁)
    rw [reassoc_of% Q_termToTotHom_comp_shiftFunctorAdd']
    exact Category.assoc _ _ _
  · change totConnectingAt L a ≫ (shiftFunctor (DerivedCategory A) (1 : ℤ)).map (𝟙 _) =
      (totShiftIso L a).hom ≫
        (-((DerivedCategory.Q.map (shiftedTruncShortComplex L a).f)⟦(1 : ℤ)⟧'))
    rw [CategoryTheory.Functor.map_id, Category.comp_id, totConnectingAt]
    rfl

/-! ### The Postnikov system of the brutal truncations -/

/-- The differential `Xₙ₊₁ ⟶ Xₙ` of the complex `… ⟶ X₂ ⟶ X₁ ⟶ X₀` in `D(A)`: the differential
`L⁻ⁿ⁻¹ ⟶ L⁻ⁿ` of `L`, placed in cohomological degree zero. -/
def termDiff (n : ℕ) : term L (n + 1) ⟶ term L n :=
  (DerivedCategory.singleFunctor A 0).map (L.d (-((n : ℤ) + 1)) (-(n : ℤ)))

/-- The canonical map `Xₙ₊₁ ⟶ Yₙ`, normalised by the sign `(-1)ⁿ⁺¹`, so that its composite with
the projection `Yₙ ⟶ Xₙ` is exactly the differential `Xₙ₊₁ ⟶ Xₙ` of the complex. -/
def termToTot (n : ℕ) : term L (n + 1) ⟶ tot L n :=
  ((n : ℤ) + 1).negOnePow •
    (termToTotAt L (-((n : ℤ) + 1)) ≫
      eqToHom (congrArg (totAt L) (show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring)))

/-- The connecting morphism `Yₙ ⟶ Yₙ₊₁[1]`, normalised by the same sign `(-1)ⁿ⁺¹` as
`termToTot`, so that the triangle `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` remains distinguished. -/
def totConnecting (n : ℕ) : tot L n ⟶ (tot L (n + 1))⟦(1 : ℤ)⟧ :=
  ((n : ℤ) + 1).negOnePow •
    (eqToHom (congrArg (totAt L) (show -(n : ℤ) = -((n : ℤ) + 1) + 1 by ring)) ≫
      totConnectingAt L (-((n : ℤ) + 1)))

/-- The brutal-truncation triangle with its third vertex presented at a degree equal to `a + 1`
and its last two morphisms scaled by a sign, which leaves it distinguished. -/
private theorem truncTriangleAt_distinguished' (a b : ℤ) (h : a + 1 = b) (u : ℤˣ) :
    Triangle.mk (totProjAt L a) (u • (termToTotAt L a ≫ eqToHom (congrArg (totAt L) h)))
        (u • (eqToHom (congrArg (totAt L) h.symm) ≫ totConnectingAt L a)) ∈
      distTriang (DerivedCategory A) := by
  subst h
  have hT : Triangle.mk (totProjAt L a) (termToTotAt L a) (totConnectingAt L a) ∈
      distTriang (DerivedCategory A) := truncTriangleAt_distinguished L a
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (unitsSmulIso u (Iso.refl _)) ?_ ?_ ?_)
  · simp
  · simp only [unitsSmulIso, Units.smul_def, Iso.refl_hom, Triangle.mk_obj₂, Triangle.mk_obj₃,
      Triangle.mk_mor₂, eqToHom_refl, Category.comp_id, Category.id_comp,
      Preadditive.comp_zsmul]
    rw [smul_smul, Int.units_coe_mul_self, one_smul]
  · simp [unitsSmulIso, Units.smul_def]

/-- **The triangles `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` are distinguished**, in the sign
normalisation of `termToTot` and `totConnecting`. -/
theorem truncTriangle_distinguished (n : ℕ) :
    Triangle.mk (totProj L (n + 1)) (termToTot L n) (totConnecting L n) ∈
      distTriang (DerivedCategory A) :=
  truncTriangleAt_distinguished' L (-((n : ℤ) + 1)) (-(n : ℤ)) (by ring)
    ((n : ℤ) + 1).negOnePow

/-- **The composite `Xₙ₊₁ ⟶ Yₙ ⟶ Xₙ` is the differential of the complex**, for the maps in the
sign normalisation of `termToTot`. -/
theorem termToTot_comp_totProj (n : ℕ) :
    termToTot L n ≫ totProj L n = termDiff L n := by
  have h : -((n : ℤ) + 1) + 1 = -(n : ℤ) := by ring
  have key := termToTotAt_comp_totProjAt' L (-((n : ℤ) + 1)) (-(n : ℤ)) h
  have step : termToTot L n ≫ totProj L n =
      (((n : ℤ) + 1).negOnePow : ℤ) •
        (termToTotAt L (-((n : ℤ) + 1)) ≫ eqToHom (congrArg (totAt L) h) ≫
          totProjAt L (-(n : ℤ))) := by
    change ((((n : ℤ) + 1).negOnePow : ℤ) •
        (termToTotAt L (-((n : ℤ) + 1)) ≫ eqToHom (congrArg (totAt L) h))) ≫
          totProjAt L (-(n : ℤ)) = _
    rw [Preadditive.zsmul_comp, Category.assoc]
  have final : (((n : ℤ) + 1).negOnePow : ℤ) •
        ((-((n : ℤ) + 1)).negOnePow •
          (DerivedCategory.singleFunctor A 0).map (L.d (-((n : ℤ) + 1)) (-(n : ℤ)))) =
      termDiff L n := by
    rw [Units.smul_def, smul_smul, ← Units.val_mul, Int.negOnePow_neg, Int.units_mul_self,
      Units.val_one, one_smul]
    rfl
  rw [step, key]
  exact final

/-! ### The shifted objects `Yₙ` against the unshifted tower of brutal truncations

The tower `truncTower` records the brutal truncations themselves, whereas `tot` records them
shifted: `tot L n = Yₙ` and `(truncTower L).obj n = Yₙ[n]`. The two presentations agree at the
bottom of the tower, where the shift is by zero. -/

/-- The identification of `Yₐ = Q(σ^{≥a}L⟦a⟧)` with the shift by `a` of the term `σ^{≥a}L` of the
tower of brutal truncations: the localization functor commutes with the shift. -/
abbrev totAtCommShiftIso (a : ℤ) :
    totAt L a ≅ (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE a)))⟦a⟧ :=
  (DerivedCategory.Q.commShiftIso a).app (L.stupidTrunc (embeddingUpIntGE a))

/-- The commutation of the localization functor with the shift by `a + 1`, split into its
commutations with the shifts by `a` and by `1`. -/
private theorem Q_commShiftIso_hom_app_add_one (M : CochainComplex A ℤ) (a : ℤ) :
    DerivedCategory.Q.map ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).hom.app M) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (M⟦a⟧) ≫
          ((DerivedCategory.Q.commShiftIso a).hom.app M)⟦(1 : ℤ)⟧' =
      (DerivedCategory.Q.commShiftIso (a + 1)).hom.app M ≫
        ((shiftFunctorAdd' (DerivedCategory A) a 1 (a + 1) rfl).app
          (DerivedCategory.Q.obj M)).hom := by
  rw [DerivedCategory.Q.commShiftIso_add' (a := a) (b := (1 : ℤ)) (c := a + 1) rfl]
  simp [CategoryTheory.Functor.CommShift.isoAdd'_hom_app]

/-- The connecting morphism of the brutal-truncation triangle, without its sign, read on the
tower through the commutation of the localization functor with the shift. -/
private theorem totConnectingAt_comp_commShiftIso_aux (a : ℤ) :
    DerivedCategory.Q.map ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).hom.app
          (L.stupidTrunc (embeddingUpIntGE (a + 1)))) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            ((L.stupidTrunc (embeddingUpIntGE (a + 1)))⟦a⟧) ≫
          ((DerivedCategory.Q.map
              ((stupidTruncGEMapLE L (show a ≤ a + 1 by omega))⟦a⟧'))⟦(1 : ℤ)⟧') ≫
            ((DerivedCategory.Q.commShiftIso a).hom.app
              (L.stupidTrunc (embeddingUpIntGE a)))⟦(1 : ℤ)⟧' =
      (DerivedCategory.Q.commShiftIso (a + 1)).hom.app
          (L.stupidTrunc (embeddingUpIntGE (a + 1))) ≫
        ((DerivedCategory.Q.map (stupidTruncGEMapLE L (show a ≤ a + 1 by omega)))⟦a + 1⟧') ≫
          ((shiftFunctorAdd' (DerivedCategory A) a 1 (a + 1) rfl).app
            (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE a)))).hom := by
  rw [← DerivedCategory.Q.commShiftIso_hom_naturality_assoc
    ((stupidTruncGEMapLE L (show a ≤ a + 1 by omega))⟦a⟧') (1 : ℤ)]
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hnat : (shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).hom.app
        (L.stupidTrunc (embeddingUpIntGE (a + 1))) ≫
      ((stupidTruncGEMapLE L (show a ≤ a + 1 by omega))⟦a⟧')⟦(1 : ℤ)⟧' =
      (stupidTruncGEMapLE L (show a ≤ a + 1 by omega))⟦a + 1⟧' ≫
        (shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).hom.app
          (L.stupidTrunc (embeddingUpIntGE a)) :=
    ((shiftFunctorAdd' (CochainComplex A ℤ) a 1 (a + 1) rfl).hom.naturality _).symm
  rw [hnat, DerivedCategory.Q.map_comp_assoc, Q_commShiftIso_hom_app_add_one,
    DerivedCategory.Q.commShiftIso_hom_naturality_assoc]

/-- Four morphisms composed with a sign on the third, rearranged. -/
private theorem neg_comp_rearrange {D : Type*} [Category D] [Preadditive D] {V W X Y Z : D}
    (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y) (k : Y ⟶ Z) :
    ((f ≫ g) ≫ (-h)) ≫ k = -(f ≫ g ≫ h ≫ k) := by
  simp

/-- A sign in the middle of a three-fold composite pulled out in front. -/
private theorem neg_comp_middle {D : Type*} [Category D] [Preadditive D] {V W X Y : D}
    (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y) : -(f ≫ g ≫ h) = f ≫ (-g) ≫ h := by
  simp

/-- **The connecting morphism `Yₐ₊₁ ⟶ Yₐ[1]` of the brutal-truncation triangle is the inclusion
`σ^{≥a+1}L ⟶ σ^{≥a}L` of one term of the tower into the next, shifted by `a + 1`**, up to the
sign the rotation of the triangle puts on it. -/
theorem totConnectingAt_comp_commShiftIso (a : ℤ) :
    totConnectingAt L a ≫ ((totAtCommShiftIso L a).hom)⟦(1 : ℤ)⟧' =
      (totAtCommShiftIso L (a + 1)).hom ≫
        (-((DerivedCategory.Q.map
            (stupidTruncGEMapLE L (show a ≤ a + 1 by omega)))⟦a + 1⟧')) ≫
          ((shiftFunctorAdd' (DerivedCategory A) a 1 (a + 1) rfl).app
            (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE a)))).hom :=
  (neg_comp_rearrange _ _ _ _).trans
    ((congrArg Neg.neg (totConnectingAt_comp_commShiftIso_aux L a)).trans
      (neg_comp_middle _ _ _))

/-- **At the bottom of the tower `Yₐ₊₁ = Y₀` is the term `σ^{≥0}L` itself**: there the shift is
by zero. -/
def totAtTowerIso (a : ℤ) (ha : a + 1 = 0) :
    totAt L (a + 1) ≅ DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE (a + 1))) :=
  totAtCommShiftIso L (a + 1) ≪≫ (shiftFunctorZero' (DerivedCategory A) (a + 1) ha).app _

/-- `totAtTowerIso` is the commutation of the localization functor with the shift by `a + 1`,
followed by the identification of the shift by `a + 1 = 0` with the identity. -/
theorem totAtTowerIso_hom (a : ℤ) (ha : a + 1 = 0) :
    (totAtTowerIso L a ha).hom =
      (totAtCommShiftIso L (a + 1)).hom ≫
        (shiftFunctorZero' (DerivedCategory A) (a + 1) ha).hom.app
          (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE (a + 1)))) :=
  rfl

/-- **At the bottom of the tower `Yₐ[1] = Y₁[1]` is the term `σ^{≥a}L` of the tower**: the two
shifts by `a` and by `1` compose to the shift by `a + 1 = 0`. -/
def totAtTowerShiftIso (a : ℤ) (ha : a + 1 = 0) :
    (totAt L a)⟦(1 : ℤ)⟧ ≅ DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE a)) :=
  (shiftFunctor (DerivedCategory A) (1 : ℤ)).mapIso (totAtCommShiftIso L a) ≪≫
    ((shiftFunctorAdd' (DerivedCategory A) a 1 (a + 1) rfl).app
      (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE a)))).symm ≪≫
    (shiftFunctorZero' (DerivedCategory A) (a + 1) ha).app _

/-- **At the bottom of the tower the connecting morphism of the brutal-truncation triangle is the
transition of the tower**, up to the sign of the rotation. -/
theorem totConnectingAt_comp_totAtTowerShiftIso (a : ℤ) (ha : a + 1 = 0) :
    totConnectingAt L a ≫ (totAtTowerShiftIso L a ha).hom =
      (totAtTowerIso L a ha).hom ≫
        (-(DerivedCategory.Q.map (stupidTruncGEMapLE L (show a ≤ a + 1 by omega)))) := by
  have hnat : ((DerivedCategory.Q.map
        (stupidTruncGEMapLE L (show a ≤ a + 1 by omega)))⟦a + 1⟧') ≫
      (shiftFunctorZero' (DerivedCategory A) (a + 1) ha).hom.app
        (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE a))) =
      (shiftFunctorZero' (DerivedCategory A) (a + 1) ha).hom.app
          (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE (a + 1)))) ≫
        DerivedCategory.Q.map (stupidTruncGEMapLE L (show a ≤ a + 1 by omega)) :=
    (shiftFunctorZero' (DerivedCategory A) (a + 1) ha).hom.naturality _
  calc totConnectingAt L a ≫ (totAtTowerShiftIso L a ha).hom
      = (totConnectingAt L a ≫ ((totAtCommShiftIso L a).hom)⟦(1 : ℤ)⟧') ≫
          ((shiftFunctorAdd' (DerivedCategory A) a 1 (a + 1) rfl).app
            (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE a)))).inv ≫
            (shiftFunctorZero' (DerivedCategory A) (a + 1) ha).hom.app
              (DerivedCategory.Q.obj (L.stupidTrunc (embeddingUpIntGE a))) :=
        (Category.assoc _ _ _).symm
    _ = (totAtTowerIso L a ha).hom ≫
          (-(DerivedCategory.Q.map (stupidTruncGEMapLE L (show a ≤ a + 1 by omega)))) := by
        rw [totConnectingAt_comp_commShiftIso, totAtTowerIso_hom]
        simp only [Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg,
          Iso.hom_inv_id_assoc, hnat]

/-- **At the bottom of the tower the connecting morphism of the brutal-truncation triangle is the
transition of the tower**, both ends transported onto the tower. -/
theorem totAtTowerIso_inv_comp_totConnectingAt (a : ℤ) (ha : a + 1 = 0) :
    (totAtTowerIso L a ha).inv ≫ totConnectingAt L a ≫ (totAtTowerShiftIso L a ha).hom =
      -(DerivedCategory.Q.map (stupidTruncGEMapLE L (show a ≤ a + 1 by omega))) := by
  rw [totConnectingAt_comp_totAtTowerShiftIso, Iso.inv_hom_id_assoc]

/-- **At the bottom of the tower the composite `X₁ ⟶ Y₀ ⟶ X₀` is the differential of the
complex**, up to the sign the shift by `a = -1` puts on it. -/
theorem termToTotAt_comp_totProjAt_of_add_one_eq_zero (a : ℤ) (ha : a + 1 = 0) :
    termToTotAt L a ≫ totProjAt L (a + 1) =
      -((DerivedCategory.singleFunctor A 0).map (L.d a (a + 1))) := by
  rw [termToTotAt_comp_totProjAt]
  have hu : a.negOnePow = (-1 : ℤˣ) := by
    have h : a = -1 := by omega
    subst h
    simp
  rw [hu, Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]

/-- **The map `Y₀ ⟶ X₀` is an isomorphism** when `L` is concentrated in degrees `≤ 0`. -/
instance isIso_totProj_zero [L.IsStrictlyLE 0] : IsIso (totProj L 0) := by
  have h : ∀ n : ℤ, IsIso ((stupidTruncGEπ L 0).f n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [stupidTruncGEπ_f]
      infer_instance
    · refine IsZero.isIso ?_ (HomologicalComplex.isZero_single_obj_X _ 0 (L.X 0) n hn) _
      rcases lt_or_gt_of_ne hn with h | h
      · exact CochainComplex.isZero_of_isStrictlyGE
          (L.stupidTrunc (embeddingUpIntGE 0)) 0 n (by omega)
      · exact IsZero.of_iso (L.isZero_of_isStrictlyLE 0 n (by omega))
          (stupidTruncGEXIso L 0 n (by omega))
  have h2 : IsIso (stupidTruncGEπ L 0) := HomologicalComplex.Hom.isIso_of_components _
  have h3 : IsIso (totProjHom L 0) := by
    rw [totProjHom]
    infer_instance
  change IsIso (DerivedCategory.Q.map (totProjHom L 0))
  infer_instance

/-- **The brutal-truncation triangles define a Postnikov system.** For a complex `L`
concentrated in degrees `≤ 0` and every length `N`, the triangles
`Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` are a Postnikov system (Derived Categories, Definition 0D7Z) for
the length-`N` truncation `X_N ⟶ ⋯ ⟶ X₁ ⟶ X₀` of the complex of terms of `L`, with
totalisation `Y_N = σ^{≥-N}L[-N]`. -/
def postnikovSystem (N : ℕ) [L.IsStrictlyLE 0] :
    Triangulated.PostnikovSystem (fun i : Fin (N + 1) => term L (i : ℕ))
      (fun i : Fin N => termDiff L (i : ℕ)) where
  obj i := tot L (i : ℕ)
  π i := totProj L (i : ℕ)
  p i := termToTot L (i : ℕ)
  δ i := totConnecting L (i : ℕ)
  isIso_π_zero := inferInstanceAs (IsIso (totProj L 0))
  distinguished i := truncTriangle_distinguished L (i : ℕ)
  p_comp_π i := termToTot_comp_totProj L (i : ℕ)

/-- The `i`-th object of `postnikovSystem L N` is `Yᵢ`. -/
@[simp]
theorem postnikovSystem_obj (N : ℕ) [L.IsStrictlyLE 0] (i : Fin (N + 1)) :
    (postnikovSystem L N).obj i = tot L (i : ℕ) :=
  rfl

/-- The `i`-th map `π` of `postnikovSystem L N` is the projection `Yᵢ ⟶ Xᵢ`. -/
@[simp]
theorem postnikovSystem_π (N : ℕ) [L.IsStrictlyLE 0] (i : Fin (N + 1)) :
    (postnikovSystem L N).π i = totProj L (i : ℕ) :=
  rfl

/-- The `i`-th map `p` of `postnikovSystem L N` is the normalised map `Xᵢ₊₁ ⟶ Yᵢ`. -/
@[simp]
theorem postnikovSystem_p (N : ℕ) [L.IsStrictlyLE 0] (i : Fin N) :
    (postnikovSystem L N).p i = termToTot L (i : ℕ) :=
  rfl

/-- The `i`-th connecting morphism of `postnikovSystem L N` is the normalised
`Yᵢ ⟶ Yᵢ₊₁[1]`. -/
@[simp]
theorem postnikovSystem_δ (N : ℕ) [L.IsStrictlyLE 0] (i : Fin N) :
    (postnikovSystem L N).δ i = totConnecting L (i : ℕ) :=
  rfl

/-- **A complex is the derived colimit of its brutal truncations**, that is
`L = hocolim Yₙ[n]`, **with the inclusions `σ^{≥-n}L ⟶ L` of the truncations as
coprojections**, when colimits over `ℕ` are exact. -/
theorem isHomotopyColimitWith_truncTower [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    [HasCoproduct (truncTower L ⋙ DerivedCategory.Q).obj] :
    IsHomotopyColimitWith (truncTower L ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj L)
      (fun n ↦ DerivedCategory.Q.map (ιStupidTrunc L (embeddingUpIntGE (-(n : ℤ))))) :=
  ((DerivedCategory.isHomotopyColimitWith_Q_obj_colimit (truncTower L)).of_iso
      (DerivedCategory.Q.mapIso (colimitTruncTowerIso L))).congr_coprojections fun n ↦ by
    rw [Functor.mapIso_hom, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (IsColimit.comp_coconePointUniqueUpToIso_hom _ (isColimitTruncTowerCocone L) n)

/-- **A complex is the derived colimit of its brutal truncations**, that is
`L = hocolim Yₙ[n]`, when colimits over `ℕ` are exact. -/
theorem isHomotopyColimit_truncTower [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    [HasCoproduct (truncTower L ⋙ DerivedCategory.Q).obj] :
    IsHomotopyColimit (truncTower L ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj L) :=
  isHomotopyColimit_of_iso (DerivedCategory.isHomotopyColimit_Q_obj_colimit (truncTower L))
    (DerivedCategory.Q.mapIso (colimitTruncTowerIso L))

end Objects

end StacksDraft.BrutalPostnikov

/-! ### The integral resolution on a simplicial site -/

namespace CategoryTheory.SimplicialSiteSituation

open StacksDraft.BrutalPostnikov

universe u

variable (S : SimplicialSiteSituation.{u})

/-- The resolution `… → g₂!ℤ → g₁!ℤ → g₀!ℤ` of Stacks 09WI, read as a cochain complex of
abelian sheaves on the total site supported in degrees `≤ 0`, with `g_{n!}ℤ` in degree `-n`. -/
def integerResolutionComplex : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ :=
  (simplicialIntegerComplex S).extend (ComplexShape.embeddingUpIntLE 0)

/-- In degree `-n` the cochain complex of the integral resolution is `g_{n!}ℤ`. -/
def integerResolutionComplexXIso (n : ℕ) :
    (integerResolutionComplex S).X (-(n : ℤ)) ≅ componentIntegerSheaf S ⦋n⦌ :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE 0) (i := n) (by simp) ≪≫
    (simplicialIntegerResolution S).degreeIso n

/-- The cochain complex of the integral resolution is concentrated in degrees `≤ 0`. -/
instance isStrictlyLE_integerResolutionComplex :
    CochainComplex.IsStrictlyLE (integerResolutionComplex S) 0 := by
  dsimp only [integerResolutionComplex]
  infer_instance

section Derived

universe z

variable [HasDerivedCategory.{z} (Sheaf S.totalTopology Ab.{u})]

/-- Colimits over `ℕ` are exact in the category of abelian sheaves on the total site. -/
instance hasExactColimitsOfShape_nat_sheafTotal :
    HasExactColimitsOfShape ℕ (Sheaf S.totalTopology Ab.{u}) :=
  (AB5OfSize_of_univLE.{0, 0, u, u} (Sheaf S.totalTopology Ab.{u})).ofShape ℕ

/-- Countable direct sums exist in the derived category of abelian sheaves on the total
site. -/
instance hasCoproduct_nat_derivedCategoryTotal
    (F : ℕ → DerivedCategory (Sheaf S.totalTopology Ab.{u})) : HasCoproduct F := by
  have h₁ : HasColimitsOfShape (Discrete (ULift.{u} ℕ))
      (DerivedCategory (Sheaf S.totalTopology Ab.{u})) :=
    Stacks.Injectives.hasCoproducts_derivedCategory _ (ULift.{u} ℕ)
  have : HasColimitsOfShape (Discrete ℕ)
      (DerivedCategory (Sheaf S.totalTopology Ab.{u})) :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)
  infer_instance

/-- The object `Xₙ = g_{n!}ℤ` of `D(𝒞_total)`, concentrated in degree zero. -/
abbrev integerResolutionTerm (n : ℕ) : DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  term (integerResolutionComplex S) n

/-- The object `Yₙ = (g_{n!}ℤ → … → g_{0!}ℤ)[-n]` of `D(𝒞_total)`. -/
abbrev integerResolutionTot (n : ℕ) : DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  tot (integerResolutionComplex S) n

/-- The canonical map `Yₙ ⟶ Xₙ`, the projection onto the bottom term `g_{n!}ℤ`. -/
abbrev integerResolutionTotProj (n : ℕ) :
    integerResolutionTot S n ⟶ integerResolutionTerm S n :=
  totProj (integerResolutionComplex S) n

/-- The identification of `Xₙ` with `g_{n!}ℤ` placed in degree zero. -/
def integerResolutionTermIso (n : ℕ) :
    integerResolutionTerm S n ≅
      (DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
        (componentIntegerSheaf S ⦋n⦌) :=
  (DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).mapIso
    (integerResolutionComplexXIso S n)

/-- The triangle `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` attached to the integral resolution is
distinguished, with `Yₙ₊₁ ⟶ Xₙ₊₁` the canonical projection onto the bottom term `g_{n+1!}ℤ`;
applying an exact functor `T` of `D(𝒞_total)` — such as `- ⊗^L_ℤ K` for an object `K` — gives
the corresponding triangle on `T(Xₙ)` and `T(Yₙ)`. -/
theorem distinguished_map_truncTriangle_integerResolution
    (T : DerivedCategory (Sheaf S.totalTopology Ab.{u}) ⥤
      DerivedCategory (Sheaf S.totalTopology Ab.{u})) [T.CommShift ℤ] [T.IsTriangulated]
    (n : ℕ) :
    T.mapTriangle.obj
        (truncTriangleAt (integerResolutionComplex S) (-((n : ℤ) + 1))) ∈
      distTriang (DerivedCategory (Sheaf S.totalTopology Ab.{u})) :=
  T.map_distinguished _ (truncTriangleAt_distinguished _ _)

/-- The system `n ↦ Yₙ[n] = (g_{n!}ℤ → … → g_{0!}ℤ)` of brutal truncations of the integral
resolution, as a system of objects of `D(𝒞_total)`. -/
abbrev integerResolutionSystem : ℕ ⥤ DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  truncTower (integerResolutionComplex S) ⋙ DerivedCategory.Q

/-- **Stacks 0D9I(2) for the constant sheaf `ℤ`.** The object of `D(𝒞_total)` represented by
the integral resolution is the derived colimit of the system `Yₙ[n]` of its brutal truncations,
**with the inclusions of the truncations as coprojections**. -/
theorem isHomotopyColimitWith_integerResolutionSystem :
    IsHomotopyColimitWith (integerResolutionSystem S)
      (DerivedCategory.Q.obj (integerResolutionComplex S))
      (fun n ↦ DerivedCategory.Q.map (ιStupidTrunc (integerResolutionComplex S)
        (embeddingUpIntGE (-(n : ℤ))))) :=
  isHomotopyColimitWith_truncTower _

/-- **Stacks 0D9I(2) for the constant sheaf `ℤ`.** The object of `D(𝒞_total)` represented by
the integral resolution is the derived colimit of the system `Yₙ[n]` of its brutal
truncations. -/
theorem isHomotopyColimit_integerResolutionSystem :
    IsHomotopyColimit (integerResolutionSystem S)
      (DerivedCategory.Q.obj (integerResolutionComplex S)) :=
  isHomotopyColimit_truncTower _

/-- **Stacks 0D9I(1).** For each length `N`, the brutal-truncation triangles
`Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` of the integral resolution are a Postnikov system (Derived
Categories, Definition 0D7Z) for `X_N ⟶ ⋯ ⟶ X₁ ⟶ X₀`, where `Xₙ = g_{n!}ℤ`. -/
def integerResolutionPostnikovSystem (N : ℕ) :
    Triangulated.PostnikovSystem
      (fun i : Fin (N + 1) => integerResolutionTerm S (i : ℕ))
      (fun i : Fin N => termDiff (integerResolutionComplex S) (i : ℕ)) :=
  postnikovSystem (integerResolutionComplex S) N

/-- **Stacks 0D9I(1).** For an exact functor `T` of `D(𝒞_total)` — such as `- ⊗^L_ℤ K` for an
object `K` of `D(𝒞_total)` — the images under `T` of the brutal-truncation triangles of the
integral resolution are a Postnikov system for `T(X_N) ⟶ ⋯ ⟶ T(X₁) ⟶ T(X₀)`. -/
@[stacks 0D9I]
def map_integerResolutionPostnikovSystem
    (T : DerivedCategory (Sheaf S.totalTopology Ab.{u}) ⥤
      DerivedCategory (Sheaf S.totalTopology Ab.{u})) [T.CommShift ℤ] [T.IsTriangulated]
    (N : ℕ) :
    Triangulated.PostnikovSystem
      (fun i : Fin (N + 1) => T.obj (integerResolutionTerm S (i : ℕ)))
      (fun i : Fin N => T.map (termDiff (integerResolutionComplex S) (i : ℕ))) :=
  (integerResolutionPostnikovSystem S N).map T

/-- **Stacks 0D9I(2).** For an exact functor `T` of `D(𝒞_total)` commuting with countable
direct sums — such as `- ⊗^L_ℤ K` for an object `K` of `D(𝒞_total)` — the object `T(ℤ)` is the
derived colimit of the system `T(Yₙ[n])`, **with the images under `T` of the inclusions of the
truncations as coprojections**. -/
theorem isHomotopyColimitWith_map_integerResolutionSystem
    (T : DerivedCategory (Sheaf S.totalTopology Ab.{u}) ⥤
      DerivedCategory (Sheaf S.totalTopology Ab.{u})) [T.CommShift ℤ] [T.IsTriangulated]
    [PreservesColimit (Discrete.functor (integerResolutionSystem S).obj) T] :
    IsHomotopyColimitWith (integerResolutionSystem S ⋙ T)
      (T.obj (DerivedCategory.Q.obj (integerResolutionComplex S)))
      (fun n ↦ T.map (DerivedCategory.Q.map (ιStupidTrunc (integerResolutionComplex S)
        (embeddingUpIntGE (-(n : ℤ)))))) :=
  (isHomotopyColimitWith_integerResolutionSystem S).map T

/-- **Stacks 0D9I(2).** For an exact functor `T` of `D(𝒞_total)` commuting with countable
direct sums — such as `- ⊗^L_ℤ K` for an object `K` of `D(𝒞_total)` — the object `T(ℤ)` is the
derived colimit of the system `T(Yₙ[n])`. -/
@[stacks 0D9I]
theorem isHomotopyColimit_map_integerResolutionSystem
    (T : DerivedCategory (Sheaf S.totalTopology Ab.{u}) ⥤
      DerivedCategory (Sheaf S.totalTopology Ab.{u})) [T.CommShift ℤ] [T.IsTriangulated]
    [PreservesColimit (Discrete.functor (integerResolutionSystem S).obj) T] :
    IsHomotopyColimit (integerResolutionSystem S ⋙ T)
      (T.obj (DerivedCategory.Q.obj (integerResolutionComplex S))) :=
  (isHomotopyColimit_integerResolutionSystem S).map T

end Derived

end CategoryTheory.SimplicialSiteSituation

end

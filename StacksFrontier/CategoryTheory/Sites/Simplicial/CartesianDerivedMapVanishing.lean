module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionDerivedTensor
import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization

/-!
# Maps out of a cartesian object of the derived category of a simplicial site

In the simplicial-site situation of Stacks 09WE let `K` and `K'` be objects of the derived
category `D(𝒞_total)` of abelian sheaves on the total site, and write `Kᵢ` for the restriction
of `K` to the `i`-th component site. **Stacks 0D9J** says that if `K` is cartesian and the groups
`Hom(Kᵢ[i], K'ᵢ)` for `i > 0` and `Hom(Kᵢ[i + 1], K'ᵢ)` for `i ≥ 0` vanish, then a map `K ⟶ K'`
whose degree-zero restriction vanishes is itself zero.

The proof is the one of the source. Stacks 0D9I presents `K` as the derived colimit of the system
`Yₙ[n] = (g_{n!}ℤ → ⋯ → g_{0!}ℤ) ⊗^L_ℤ K`, whose successive quotients are the shifted terms
`Xₙ[n]` of `Xₙ = g_{n!}ℤ ⊗^L_ℤ K`. The restriction of the given map to each `Yₙ[n]` vanishes, by
induction along the brutal-truncation triangles, and the map itself then vanishes because there
is no nonzero map to `K'` from the shifted direct sum in the defining triangle of the derived
colimit.

## Main results

* `StacksDraft.BrutalPostnikov.eq_zero_of_isHomotopyColimit_mapTruncTowerSystem`: the nullity
  criterion itself, for an arbitrary complex concentrated in degrees `≤ 0` and an arbitrary
  exact functor of its derived category in place of `- ⊗^L_ℤ K`.
* `StacksDraft.BrutalPostnikov.exists_distTriang_mapTruncTowerSystem`: the brutal-truncation
  triangles that criterion runs on, in the same generality.
* `StacksDraft.BrutalPostnikov.exists_distTriang_mapTruncTowerSystem_invRotate`: the same
  triangles inverse-rotated, the shape the construction step of Stacks 0D9K consumes.
* `StacksDraft.BrutalPostnikov.exists_hom_of_mapTruncTowerSystem`: the construction step itself,
  taking the extension of the given map over the first transition of the tower as a hypothesis —
  the only part of it the source's omitted computation is needed for.
* `StacksDraft.BrutalPostnikov.exists_distTriang_mapTruncTowerSystem_bottom`: the triangle at the
  bottom of the tower **with its first morphism named**, which is what the extension hypothesis
  has to be produced from.
* `StacksDraft.BrutalPostnikov.exists_factor_mapTruncTowerSystem`: that extension, produced from
  the vanishing of `T(X₁) ⟶ T(X₀) ⟶ K'`.
* `StacksDraft.BrutalPostnikov.exists_hom_of_termDiff_comp_eq_zero`: the construction step with
  both of its inputs in the form the source states them — the vanishing of the composite through
  the differential, and hypothesis (2) of Stacks 0D9K.
* `CategoryTheory.SimplicialSiteSituation.integerResolutionTensorTermIso`: for a cartesian `K`
  the term `Xᵢ = g_{i!}ℤ ⊗^L_ℤ K` of the Postnikov system of Stacks 0D9I is `g_{i!}Kᵢ`, by
  Stacks 0D9E (1).
* `CategoryTheory.SimplicialSiteSituation.eq_zero_of_derivedComponent_zero`: **Stacks 0D9J**.

## Implementation notes

The criterion is proved for an arbitrary complex `L` with `L.IsStrictlyLE 0` and an arbitrary
exact functor `T` of `D(A)`, as in
`StacksFrontier/CategoryTheory/Sites/Simplicial/IntegerResolutionPostnikov.lean` and
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleResolutionPostnikov.lean`,
which state the Postnikov system and the derived colimit in that generality: the source's proof
uses nothing about `T` beyond exactness, and nothing about `L` beyond the brutal-truncation
triangles. Tag 0D9J is the instance `L = ` the integral resolution, `T = - ⊗^L_ℤ K`;
Tag 0D9R (`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedModuleNullity.lean`) is
the instance `L = ` the module resolution of Stacks 0D9B, `T = - ⊗^L_O K`.

The source identifies `Xₙ` with `g_{n!}Kₙ` by Stacks 0D9E and then computes `Hom(Xₙ[t], K')` as
`Hom(Kₙ[t], K'ₙ)` by the adjunction `g_{n!} ⊣ g_n^{-1}`. That identification is
`integerResolutionTensorTermIso`: Stacks 0D9E (1)
(`CategoryTheory.SimplicialSiteSituation.isCartesianDerived_iff_isIso_integerProjection`) makes
the projection map invertible for a cartesian `K`, and
`derivedTensorIntegerResolutionTermIso` identifies the term of the Postnikov system with its
target. The two uses the source makes of it are
`hom_integerResolutionTensorTerm_eq_zero` — the vanishing of `Hom(Xᵢ[t], K')` whenever
`Hom(Kᵢ[t], K'ᵢ)` vanishes — and `comp_eq_zero_of_derivedComponent_map_eq_zero` — a map
`X₀ ⟶ K` followed by a map `K ⟶ K'` with zero degree-zero restriction is zero.

The brutal-truncation triangle is taken in its unshifted form, as the derived triangle of the
degreewise split short exact sequence `0 ⟶ σ^{≥a+1}L ⟶ σ^{≥a}L ⟶ Lᵃ[-a] ⟶ 0` at
`a = -(n + 1)`: its first two vertices are then *literally* the two consecutive terms of the
system whose derived colimit is `K`, and only the third vertex has to be identified, through
`SingleFunctors.shiftIso`, with the shift `Xₙ₊₁[n + 1]`. This is why the rotated form
`CategoryTheory.SimplicialSiteSituation.distinguished_map_truncTriangle_integerResolution`,
which the Postnikov system uses, is not the one used here.

## References

* [Stacks Project, Tag 0D9J](https://stacks.math.columbia.edu/tag/0D9J)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open StacksDraft.BrutalPostnikov StacksDraft.StupidTruncation
open scoped Simplicial

universe w v u

namespace CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Vanishing of `Hom(X⟦a⟧, Y)` depends on the shift `a` only through its value. -/
private theorem eq_zero_of_shift_eq' {X Y : D} {a a' : ℤ} (haa' : a = a')
    (h : ∀ u : X⟦a⟧ ⟶ Y, u = 0) (u : X⟦a'⟧ ⟶ Y) : u = 0 := by
  subst haa'; exact h u

/-- If every map `X⟦c⟧ ⟶ Y` vanishes then so does every map `X⟦a⟧⟦b⟧ ⟶ Y`, for `a + b = c`. -/
private theorem eq_zero_of_shift_shift {E : Type*} [Category E] [Preadditive E] [HasShift E ℤ]
    {X Y : E} (a b c : ℤ) (h : a + b = c)
    (hc : ∀ v : X⟦c⟧ ⟶ Y, v = 0) (u : X⟦a⟧⟦b⟧ ⟶ Y) : u = 0 :=
  hom_eq_zero_of_iso ((shiftFunctorAdd' E a b c h).app X).symm (Iso.refl Y) hc u

omit [HasZeroObject D] [Pretriangulated D] in
/-- If every map `X⟦a⟧ ⟶ Y` vanishes then so does every map `X ⟶ Y⟦b⟧`, for `a + b = 0`. -/
private theorem eq_zero_of_shift_target {X Y : D} (a b : ℤ) (hab : a + b = 0)
    (h : ∀ v : X⟦a⟧ ⟶ Y, v = 0) (u : X ⟶ Y⟦b⟧) : u = 0 := by
  apply (shiftFunctor D a).map_injective
  rw [Functor.map_zero,
    ← cancel_mono ((shiftFunctorCompIsoId D b a (by omega)).app Y).hom, zero_comp]
  exact h _

omit [HasZeroObject D] [Pretriangulated D] in
/-- If every map `X ⟶ Y⟦b⟧` vanishes then so does every map `X⟦a⟧ ⟶ Y`, for `a + b = 0`. -/
private theorem eq_zero_of_shift_source {X Y : D} (a b : ℤ) (hab : a + b = 0)
    (h : ∀ v : X ⟶ Y⟦b⟧, v = 0) (u : X⟦a⟧ ⟶ Y) : u = 0 := by
  apply (shiftFunctor D b).map_injective
  rw [Functor.map_zero, ← cancel_epi ((shiftFunctorCompIsoId D a b hab).app X).inv, comp_zero]
  exact h _

/-- **Exactness of `Hom(-, W)`.** If no nonzero map goes from the first or the third vertex of a
distinguished triangle to `W`, then none goes from the second one. -/
private theorem eq_zero_hom_obj₂' {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h₁ : ∀ u : T.obj₁ ⟶ W, u = 0) (h₃ : ∀ u : T.obj₃ ⟶ W, u = 0) (u : T.obj₂ ⟶ W) : u = 0 := by
  obtain ⟨v, hv⟩ := T.yoneda_exact₂ hT u (h₁ _)
  rw [hv, h₃ v, comp_zero]

/-- The shift of the previous statement: the triangle rotated three times has the shifts of the
three vertices in the same order. -/
private theorem eq_zero_hom_obj₂_shift {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h₁ : ∀ u : T.obj₁⟦(1 : ℤ)⟧ ⟶ W, u = 0) (h₃ : ∀ u : T.obj₃⟦(1 : ℤ)⟧ ⟶ W, u = 0)
    (u : T.obj₂⟦(1 : ℤ)⟧ ⟶ W) : u = 0 :=
  eq_zero_hom_obj₂' (rot_of_distTriang _ (rot_of_distTriang _ (rot_of_distTriang _ hT)))
    h₁ h₃ u

/-- A distinguished triangle stays distinguished when its third vertex is replaced by an
isomorphic object. -/
private theorem distTriang_of_iso_obj₃ {T : Triangle D} (hT : T ∈ distTriang D) {Z : D}
    (e : T.obj₃ ≅ Z) :
    Triangle.mk T.mor₁ (T.mor₂ ≫ e.hom) (e.inv ≫ T.mor₃) ∈ distTriang D :=
  isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp) (by simp))

/-- A distinguished triangle stays distinguished when its second and third vertices are both
replaced by isomorphic objects. -/
private theorem distTriang_of_iso_obj₂₃ {T : Triangle D} (hT : T ∈ distTriang D) {Y Z : D}
    (e₂ : T.obj₂ ≅ Y) (e₃ : T.obj₃ ≅ Z) :
    Triangle.mk (T.mor₁ ≫ e₂.hom) (e₂.inv ≫ T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃) ∈
      distTriang D :=
  isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) e₂.symm e₃.symm (by simp) (by simp) (by simp))

/-- **Negating the last two morphisms of a distinguished triangle leaves it distinguished**: it
is the transport along the automorphism `-𝟙` of the third vertex. -/
private theorem distTriang_neg_mor₂₃ {T : Triangle D} (hT : T ∈ distTriang D) :
    Triangle.mk T.mor₁ (-T.mor₂) (-T.mor₃) ∈ distTriang D :=
  isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ⟨-𝟙 T.obj₃, -𝟙 T.obj₃, by simp, by simp⟩ (by simp) (by simp) (by simp))

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- Two morphisms whose composite is minus a map annihilating `b` compose to zero against `b`,
with an isomorphism inserted and cancelled in the middle. -/
private theorem comp_iso_cancel_comp_eq_zero {V W X Y Z : D} (f : V ⟶ W) (e : W ≅ Z)
    (g : W ⟶ X) (d : V ⟶ X) (b : X ⟶ Y) (hd : f ≫ g = -d) (hb : d ≫ b = 0) :
    (f ≫ e.hom) ≫ (e.inv ≫ g ≫ b) = 0 := by
  rw [Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp,
    ← Category.assoc, hd, Preadditive.neg_comp, hb, neg_zero]

/-- The second morphism of a distinguished triangle may be replaced by an equal one. -/
private theorem distTriang_mor₂_eq {X Y Z : D} {f : X ⟶ Y} {g g' : Y ⟶ Z}
    {h : Z ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang D) (hg : g = g') :
    Triangle.mk f g' h ∈ distTriang D :=
  hg ▸ hT

end CategoryTheory.Pretriangulated

namespace StacksDraft.BrutalPostnikov

variable {A : Type u} [Category.{v} A] [Abelian A] (L : CochainComplex A ℤ)

/-- The projection of a brutal truncation onto its bottom term is an isomorphism as soon as the
complex is concentrated in degrees `≤ p`: in degree `p` the projection is the identification of
the terms, below `p` the truncation vanishes, and above `p` both sides do. -/
theorem isIso_stupidTruncGEπ (p : ℤ) [L.IsStrictlyLE p] : IsIso (stupidTruncGEπ L p) := by
  have h : ∀ n : ℤ, IsIso ((stupidTruncGEπ L p).f n) := by
    intro n
    by_cases hn : n = p
    · subst hn
      rw [stupidTruncGEπ_f]
      infer_instance
    · refine IsZero.isIso ?_ (HomologicalComplex.isZero_single_obj_X _ p (L.X p) n hn) _
      rcases lt_or_gt_of_ne hn with h | h
      · exact CochainComplex.isZero_of_isStrictlyGE
          (L.stupidTrunc (ComplexShape.embeddingUpIntGE p)) p n (by omega)
      · exact IsZero.of_iso (L.isZero_of_isStrictlyLE p n (by omega))
          (stupidTruncGEXIso L p n (by omega))
  exact HomologicalComplex.Hom.isIso_of_components _

variable [HasDerivedCategory.{w} A]

/-- **The brutal-truncation triangle** `σ^{≥b}L ⟶ σ^{≥a}L ⟶ Lᵃ[-a]` is distinguished in `D(A)`,
for `b = a + 1`: it is the triangle of the degreewise split short exact sequence of
`stupidTruncGEShortComplex`. Only the first two morphisms are named; the connecting morphism is
not used. -/
theorem exists_distTriang_stupidTruncGE (a b : ℤ) (hab : a + 1 = b) (hle : a ≤ b) :
    ∃ δ, Triangle.mk (DerivedCategory.Q.map (stupidTruncGEMapLE L hle))
        (DerivedCategory.Q.map (stupidTruncGEπ L a)) δ ∈ distTriang (DerivedCategory A) := by
  subst hab
  exact ⟨_, distinguished_mapTriangle_degreewiseSplit _ (truncSplitting L a)⟩

/-! ### The image under an exact functor of the tower of brutal truncations -/

section MapTruncTower

/-- The system `n ↦ T(Yₙ[n])`: the image under a functor `T` of `D(A)` of the tower of brutal
truncations `σ^{≥-n}L` of `L`, read in `D(A)`. For `T = - ⊗^L K` this is the system of
Stacks 0D9I and Stacks 0D9Q whose derived colimit is `K`. -/
abbrev mapTruncTowerSystem (T : DerivedCategory A ⥤ DerivedCategory A) :
    ℕ ⥤ DerivedCategory A :=
  (truncTower L ⋙ DerivedCategory.Q) ⋙ T

variable (T : DerivedCategory A ⥤ DerivedCategory A) [T.CommShift ℤ] [T.IsTriangulated]

/-- **The degree-zero term of the system is `T(X₀)`.** The complex is concentrated in degrees
`≤ 0`, so its brutal truncation in degree `0` is its bottom term. -/
def mapTruncTowerObjZeroIso [L.IsStrictlyLE 0] :
    (mapTruncTowerSystem L T).obj 0 ≅ T.obj (term L 0) := by
  have : CochainComplex.IsStrictlyLE L (-((0 : ℕ) : ℤ)) := by
    simpa using (inferInstance : CochainComplex.IsStrictlyLE L 0)
  have hiso := isIso_stupidTruncGEπ L (-((0 : ℕ) : ℤ))
  exact T.mapIso (DerivedCategory.Q.mapIso (@asIso _ _ _ _ _ hiso))

/-- **The third vertex of the brutal-truncation triangle in degree `n + 1` is `T(Xₙ₊₁)[n + 1]`.**
The bottom term of the truncation sits in cohomological degree `-(n + 1)`, and
`SingleFunctors.shiftIso` moves it to degree zero; `T` commutes with the shift. -/
def mapTruncTowerQuotientIso (n : ℕ) :
    T.obj ((DerivedCategory.singleFunctor A (-((n + 1 : ℕ) : ℤ))).obj
        (L.X (-((n + 1 : ℕ) : ℤ)))) ≅
      (T.obj (term L (n + 1)))⟦((n + 1 : ℕ) : ℤ)⟧ :=
  T.mapIso ((((DerivedCategory.singleFunctors A).shiftIso
      ((n + 1 : ℕ) : ℤ) (-((n + 1 : ℕ) : ℤ)) 0 (by omega)).app
        (L.X (-((n + 1 : ℕ) : ℤ)))).symm) ≪≫
    (T.commShiftIso ((n + 1 : ℕ) : ℤ)).app (term L (n + 1))

/-- **The brutal-truncation triangle in degree `n + 1`, with its third vertex presented as
`T(Xₙ₊₁)[n + 1]`:** the triangle `T(Yₙ[n]) ⟶ T(Yₙ₊₁[n + 1]) ⟶ T(Xₙ₊₁)[n + 1]` is
distinguished, its first morphism being the transition of the system. -/
theorem exists_distTriang_mapTruncTowerSystem (n : ℕ) :
    ∃ (m₂ : (mapTruncTowerSystem L T).obj (n + 1) ⟶
        (T.obj (term L (n + 1)))⟦((n + 1 : ℕ) : ℤ)⟧)
      (δ : (T.obj (term L (n + 1)))⟦((n + 1 : ℕ) : ℤ)⟧ ⟶
        ((mapTruncTowerSystem L T).obj n)⟦(1 : ℤ)⟧),
      Triangle.mk ((mapTruncTowerSystem L T).map (homOfLE (Nat.le_succ n))) m₂ δ ∈
        distTriang (DerivedCategory A) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_stupidTruncGE L
    (-((n + 1 : ℕ) : ℤ)) (-((n : ℕ) : ℤ)) (by omega) (by omega)
  have hT := T.map_distinguished _ hδ
  exact ⟨_, _, distTriang_of_iso_obj₃ hT (mapTruncTowerQuotientIso L T n)⟩

/-- **The brutal-truncation triangle in degree `n + 1`, inverse-rotated**: the triangle
`T(Xₙ₊₁)[n + 1][-1] ⟶ T(Yₙ[n]) ⟶ T(Yₙ₊₁[n + 1])` is distinguished, its *second* morphism being
the transition of the system. This is the form the construction step of Stacks 0D9K consumes,
`CategoryTheory.Triangulated.exists_hom_of_telescope` asking for the transition as the second
morphism of the triangle rather than as the first. -/
theorem exists_distTriang_mapTruncTowerSystem_invRotate (n : ℕ) :
    ∃ (w : ((T.obj (term L (n + 1)))⟦((n + 1 : ℕ) : ℤ)⟧)⟦(-1 : ℤ)⟧ ⟶
        (mapTruncTowerSystem L T).obj n)
      (r : (mapTruncTowerSystem L T).obj (n + 1) ⟶
        (((T.obj (term L (n + 1)))⟦((n + 1 : ℕ) : ℤ)⟧)⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧),
      Triangle.mk w ((mapTruncTowerSystem L T).map (homOfLE (Nat.le_succ n))) r ∈
        distTriang (DerivedCategory A) := by
  obtain ⟨m₂, δ, hT⟩ := exists_distTriang_mapTruncTowerSystem L T n
  exact ⟨_, _, inv_rot_of_distTriang _ hT⟩

/-- **The nullity criterion of Stacks 0D9J and 0D9R, in brutal-truncation form.** Let `L` be a
complex concentrated in degrees `≤ 0`, let `T` be an exact functor of `D(A)` and let `K` be a
derived colimit of the system `T(Yₙ[n])` of the images of the brutal truncations of `L`. If
every map `T(Xₙ)[n] ⟶ K'` vanishes for `n > 0` and every map `T(Xₙ)[n + 1] ⟶ K'` vanishes for
`n ≥ 0`, then a map `f : K ⟶ K'` annihilating every map out of `T(X₀)` is zero. -/
theorem eq_zero_of_isHomotopyColimit_mapTruncTowerSystem [L.IsStrictlyLE 0]
    [HasCoproduct (mapTruncTowerSystem L T).obj] {K K' : DerivedCategory A}
    (hcolim : IsHomotopyColimit (mapTruncTowerSystem L T) K)
    (hXzero : ∀ i : ℕ, 0 < i → ∀ g : (T.obj (term L i))⟦(i : ℤ)⟧ ⟶ K', g = 0)
    (hXsucc : ∀ i : ℕ, ∀ g : (T.obj (term L i))⟦((i : ℤ) + 1)⟧ ⟶ K', g = 0)
    {f : K ⟶ K'} (hf : ∀ c : T.obj (term L 0) ⟶ K, c ≫ f = 0) :
    f = 0 := by
  have hshift : ∀ n : ℕ, ∀ v : ((mapTruncTowerSystem L T).obj n)⟦(1 : ℤ)⟧ ⟶ K', v = 0 := by
    intro n
    induction n with
    | zero =>
      intro v
      refine hom_eq_zero_of_iso ((shiftFunctor (DerivedCategory A) (1 : ℤ)).mapIso
        (mapTruncTowerObjZeroIso L T)) (Iso.refl K') ?_ v
      exact fun u => eq_zero_of_shift_eq' (by norm_num) (hXsucc 0) u
    | succ n ih =>
      intro v
      obtain ⟨m₂, δ, hT⟩ := exists_distTriang_mapTruncTowerSystem L T n
      refine eq_zero_hom_obj₂_shift hT (fun u => ih u) ?_ v
      exact eq_zero_of_shift_shift _ _ _ rfl (hXsucc (n + 1))
  obtain ⟨p, q, hT⟩ := hcolim
  have hstep : ∀ n : ℕ, Sigma.ι (mapTruncTowerSystem L T).obj n ≫ p ≫ f =
      (mapTruncTowerSystem L T).map (homOfLE (Nat.le_succ n)) ≫
        Sigma.ι (mapTruncTowerSystem L T).obj (n + 1) ≫ p ≫ f := by
    intro n
    have h0 := comp_distTriang_mor_zero₁₂ _ hT
    have h1 := congrArg (fun g => Sigma.ι (mapTruncTowerSystem L T).obj n ≫ g ≫ f) h0
    simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, colimit.ι_desc_assoc, Cofan.mk_pt,
      Cofan.mk_ι_app, Preadditive.sub_comp, Category.assoc, zero_comp, comp_zero] at h1
    exact sub_eq_zero.1 h1
  have hzero : ∀ n : ℕ, Sigma.ι (mapTruncTowerSystem L T).obj n ≫ p ≫ f = 0 := by
    intro n
    induction n with
    | zero =>
      have := hf ((mapTruncTowerObjZeroIso L T).inv ≫
        Sigma.ι (mapTruncTowerSystem L T).obj 0 ≫ p)
      have h2 := congrArg (fun g => (mapTruncTowerObjZeroIso L T).hom ≫ g) this
      simpa using h2
    | succ n ih =>
      obtain ⟨m₂, δ, hT'⟩ := exists_distTriang_mapTruncTowerSystem L T n
      obtain ⟨v, hv⟩ := Triangle.yoneda_exact₂ _ hT'
          (Sigma.ι (mapTruncTowerSystem L T).obj (n + 1) ≫ p ≫ f)
          (by simp only [Triangle.mk_mor₁]; rw [← hstep n]; exact ih)
      rw [hv, hXzero (n + 1) (Nat.succ_pos n) v, comp_zero]
  have hsum : ∀ v : (∐ (mapTruncTowerSystem L T).obj)⟦(1 : ℤ)⟧ ⟶ K', v = 0 := by
    refine eq_zero_of_shift_source 1 (-1) (by omega) ?_
    intro v
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [comp_zero]
    exact eq_zero_of_shift_target 1 (-1) (by omega) (hshift n) _
  have hpf : p ≫ f = 0 := Sigma.hom_ext _ _ fun n => by rw [comp_zero]; exact hzero n
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hT f hpf
  rw [hg, hsum g, comp_zero]

/-- **A map out of the bottom of the brutal-truncation tower extends to the derived colimit**,
the degree-zero extension being taken as a hypothesis. Let `L` be a complex concentrated in
degrees `≤ 0`, let `T` be an exact functor of `D(A)` and let `K` be a derived colimit of the
system `T(Yₙ[n])` of the images of the brutal truncations, with its coprojections recorded. A
map `a : T(Y₀[0]) ⟶ K'` which extends along the first transition of the tower, in a situation
where every map `T(Xₙ₊₁)[n] ⟶ K'` with `n > 0` vanishes, extends to the whole of `K`.

This is the construction step of Stacks 0D9K in the form the brutal-truncation presentation of
Stacks 0D9I hands it over: `CategoryTheory.Triangulated.exists_hom_of_telescope` asks for the
vanishing of the composite with the first map of each triangle, and at the bottom of the tower
that vanishing is equivalent to the extension hypothesis, because the first two maps of a
distinguished triangle compose to zero. Above the bottom it is supplied by the vanishing
hypothesis, read through the comparison of the iterated shift `(Xₙ₊₁[n + 1])[-1]` with
`Xₙ₊₁[n]`. -/
theorem exists_hom_of_mapTruncTowerSystem [L.IsStrictlyLE 0]
    [HasCoproduct (mapTruncTowerSystem L T).obj] {K K' : DerivedCategory A}
    {c : ∀ n, (mapTruncTowerSystem L T).obj n ⟶ K}
    (hK : IsHomotopyColimitWith (mapTruncTowerSystem L T) K c)
    (a : (mapTruncTowerSystem L T).obj 0 ⟶ K')
    (hfactor : ∃ c₁ : (mapTruncTowerSystem L T).obj 1 ⟶ K',
      (mapTruncTowerSystem L T).map (homOfLE (Nat.le_succ 0)) ≫ c₁ = a)
    (hvanish : ∀ i : ℕ, 0 < i → ∀ g : (T.obj (term L (i + 1)))⟦(i : ℤ)⟧ ⟶ K', g = 0) :
    ∃ γ : K ⟶ K', c 0 ≫ γ = a := by
  obtain ⟨p, q, hT, hc⟩ := hK
  choose w r hW using exists_distTriang_mapTruncTowerSystem_invRotate L T
  have ha : w 0 ≫ a = 0 := by
    obtain ⟨c₁, hc₁⟩ := hfactor
    have hz : w 0 ≫ (mapTruncTowerSystem L T).map (homOfLE (Nat.le_succ 0)) = 0 :=
      comp_distTriang_mor_zero₁₂ _ (hW 0)
    rw [← hc₁, ← Category.assoc, hz, zero_comp]
  have hvanish' : ∀ n : ℕ, 0 < n →
      ∀ g : ((T.obj (term L (n + 1)))⟦((n + 1 : ℕ) : ℤ)⟧)⟦(-1 : ℤ)⟧ ⟶ K', g = 0 := by
    intro n hn
    exact eq_zero_of_shift_shift _ _ _ (by push_cast; ring) (hvanish n hn)
  obtain ⟨γ, hγ⟩ := CategoryTheory.Triangulated.exists_hom_of_telescope
    (mapTruncTowerSystem L T) _ w r hW p q hT a ha hvanish'
  exact ⟨γ, by rw [← hγ, ← Category.assoc, hc 0]⟩

/-! ### The degree-zero extension, from the differential of the complex

`exists_hom_of_mapTruncTowerSystem` takes the extension along the first transition of the tower
as a hypothesis, and that hypothesis cannot be produced from
`exists_distTriang_mapTruncTowerSystem_invRotate`: the triangle there has its first morphism
quantified away, and the extension is exactly the statement that composing with that morphism
kills the map. So the triangle has to be produced again with its first morphism named, which the
*shifted* presentation of the brutal truncations supplies: `termToTotAt` is the canonical map
`Xₙ₊₁ ⟶ Yₙ`, the rotation of `truncTriangleAt` has it as its first morphism, and
`termToTotAt_comp_totProjAt` computes its composite with the projection `Yₙ ⟶ Xₙ` as the
differential of the complex. The two presentations are compared at the bottom of the tower by
`StacksDraft.BrutalPostnikov.totAtTowerIso` and
`StacksDraft.BrutalPostnikov.totAtTowerIso_inv_comp_totConnectingAt`, where the shift is by
zero. -/

/-- **The brutal-truncation triangle at the bottom of the tower, with its first morphism
named**: the triangle `T(X₁) ⟶ T(Y₀) ⟶ T(Y₁[1])` whose first morphism is the canonical map
`X₁ ⟶ Y₀` of the shifted presentation and whose second morphism is the first transition of the
tower. Only the connecting morphism is quantified away. -/
theorem exists_distTriang_mapTruncTowerSystem_bottom (a : ℤ) (ha : a + 1 = 0) :
    ∃ δ, Triangle.mk (T.map (termToTotAt L a) ≫ T.map (totAtTowerIso L a ha).hom)
        (T.map (DerivedCategory.Q.map
          (stupidTruncGEMapLE L (show a ≤ a + 1 by omega)))) δ ∈
      distTriang (DerivedCategory A) := by
  have hrot : T.mapTriangle.obj (truncTriangleAt L a).rotate ∈ distTriang (DerivedCategory A) :=
    T.map_distinguished _ (rot_of_distTriang _ (truncTriangleAt_distinguished L a))
  have h2 := distTriang_neg_mor₂₃ (distTriang_of_iso_obj₂₃ hrot
    (T.mapIso (totAtTowerIso L a ha)) (T.mapIso (totAtTowerShiftIso L a ha)))
  have hm2 : -(T.map (totAtTowerIso L a ha).inv ≫ T.map (totConnectingAt L a) ≫
        T.map (totAtTowerShiftIso L a ha).hom) =
      T.map (DerivedCategory.Q.map (stupidTruncGEMapLE L (show a ≤ a + 1 by omega))) := by
    rw [← T.map_comp, ← T.map_comp, totAtTowerIso_inv_comp_totConnectingAt, T.map_neg, neg_neg]
  exact ⟨_, distTriang_mor₂_eq h2 hm2⟩

/-- **A map out of the degree-zero term of the complex which the differential annihilates extends
along the first transition of the brutal-truncation tower.** This is the extension hypothesis of
`exists_hom_of_mapTruncTowerSystem`, produced from the vanishing of `T(X₁) ⟶ T(X₀) ⟶ K'`. -/
theorem exists_factor_mapTruncTowerSystem {K' : DerivedCategory A}
    (b : T.obj (term L 0) ⟶ K') (hb : T.map (termDiff L 0) ≫ b = 0) :
    ∃ c₁ : (mapTruncTowerSystem L T).obj 1 ⟶ K',
      (mapTruncTowerSystem L T).map (homOfLE (Nat.le_succ 0)) ≫ c₁ =
        T.map (totAtTowerIso L (-((1 : ℕ) : ℤ)) (by simp)).inv ≫
          T.map (totProj L 0) ≫ b := by
  have ha : (-((1 : ℕ) : ℤ)) + 1 = 0 := by simp
  have hd : T.map (termToTotAt L (-((1 : ℕ) : ℤ))) ≫
        T.map (totProjAt L ((-((1 : ℕ) : ℤ)) + 1)) = -(T.map (termDiff L 0)) :=
    (((T.map_comp _ _).symm.trans (congrArg T.map
      (termToTotAt_comp_totProjAt_of_add_one_eq_zero L (-((1 : ℕ) : ℤ)) ha))).trans
        T.map_neg)
  have hvan := comp_iso_cancel_comp_eq_zero (T.map (termToTotAt L (-((1 : ℕ) : ℤ))))
    (T.mapIso (totAtTowerIso L (-((1 : ℕ) : ℤ)) ha))
    (T.map (totProjAt L ((-((1 : ℕ) : ℤ)) + 1))) (T.map (termDiff L 0)) b hd hb
  obtain ⟨δ, hδ⟩ := exists_distTriang_mapTruncTowerSystem_bottom L T (-((1 : ℕ) : ℤ)) ha
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ hδ _ hvan
  exact ⟨g, hg.symm⟩

/-- **A map out of the degree-zero term of the complex which the differential annihilates extends
to the derived colimit of the brutal-truncation tower.** Let `L` be a complex concentrated in
degrees `≤ 0`, `T` an exact functor of `D(A)` and `K` a derived colimit of the system `T(Yₙ[n])`
with its coprojections recorded. A map `b : T(X₀) ⟶ K'` annihilated by the differential
`T(X₁) ⟶ T(X₀)`, in a situation where every map `T(Xₙ₊₁)[n] ⟶ K'` with `n > 0` vanishes, extends
to the whole of `K`.

This is the construction step of Stacks 0D9K with both of its inputs in the form the source
states them: the first of the source's two "computation (omitted)" steps is the vanishing `hb`,
and the vanishing hypothesis (2) of Stacks 0D9K is `hvanish`. -/
theorem exists_hom_of_termDiff_comp_eq_zero [L.IsStrictlyLE 0]
    [HasCoproduct (mapTruncTowerSystem L T).obj] {K K' : DerivedCategory A}
    {c : ∀ n, (mapTruncTowerSystem L T).obj n ⟶ K}
    (hK : IsHomotopyColimitWith (mapTruncTowerSystem L T) K c)
    (b : T.obj (term L 0) ⟶ K') (hb : T.map (termDiff L 0) ≫ b = 0)
    (hvanish : ∀ i : ℕ, 0 < i → ∀ g : (T.obj (term L (i + 1)))⟦(i : ℤ)⟧ ⟶ K', g = 0) :
    ∃ γ : K ⟶ K', c 0 ≫ γ =
      T.map (totAtTowerIso L (-((1 : ℕ) : ℤ)) (by simp)).inv ≫ T.map (totProj L 0) ≫ b :=
  exists_hom_of_mapTruncTowerSystem L T hK _
    (exists_factor_mapTruncTowerSystem L T b hb) hvanish

end MapTruncTower

end StacksDraft.BrutalPostnikov

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  CategoryTheory.SimplicialSiteSituation.componentLowerShriekDerived

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.componentLowerShriekDerived_additive
  CategoryTheory.SimplicialSiteSituation.derivedComponent_additive

variable (S : SimplicialSiteSituation.{u})
  (K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u}))

/-- The object `Xₙ = g_{n!}ℤ ⊗^L_ℤ K` of `D(𝒞_total)`, the `n`-th term of the Postnikov system
of Stacks 0D9I attached to `K`. -/
abbrev integerResolutionTensorTerm (n : ℕ) : DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  (integerDerivedTensorRight S K).obj (integerResolutionTerm S n)

/-- The system `n ↦ Yₙ[n] = (g_{n!}ℤ → ⋯ → g_{0!}ℤ) ⊗^L_ℤ K` of Stacks 0D9I, whose derived
colimit is `K`. -/
abbrev integerResolutionTensorSystem : ℕ ⥤ DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  integerResolutionSystem S ⋙ integerDerivedTensorRight S K

/-- **For a cartesian `K` the term `Xᵢ = g_{i!}ℤ ⊗^L_ℤ K` of the Postnikov system of
Stacks 0D9I is the lower shriek image `g_{i!}Kᵢ` of the degree-`i` restriction of `K`.** This is
Stacks 0D9E (1): its projection map is invertible because `K` is cartesian, and
`derivedTensorIntegerResolutionTermIso` identifies the term of the system with the target of that
map. -/
noncomputable def integerResolutionTensorTermIso (hK : IsCartesianDerived S K) (i : ℕ) :
    integerResolutionTensorTerm S K i ≅
      (S.componentLowerShriekDerived ⦋i⦌).obj ((derivedComponent S ⦋i⦌).obj K) :=
  have := (isCartesianDerived_iff_isIso_integerProjection S K).1 hK ⦋i⦌
  derivedTensorIntegerResolutionTermIso S K i ≪≫ (asIso (S.integerProjection K ⦋i⦌)).symm

/-- **`Hom(Xᵢ[t], K')` vanishes as soon as `Hom(Kᵢ[t], K'ᵢ)` does**, for a cartesian `K`: the
term `Xᵢ` of the Postnikov system is `g_{i!}Kᵢ` by Stacks 0D9E, lower shriek on derived
categories commutes with the shift, and `g_{i!} ⊣ g_i^{-1}` turns a map out of `g_{i!}(Kᵢ[t])`
into a map `Kᵢ[t] ⟶ K'ᵢ`. -/
theorem hom_integerResolutionTensorTerm_eq_zero (hK : IsCartesianDerived S K) (i : ℕ) (t : ℤ)
    (h : ∀ g : ((derivedComponent S ⦋i⦌).obj K)⟦t⟧ ⟶ (derivedComponent S ⦋i⦌).obj K', g = 0) :
    ∀ g : (integerResolutionTensorTerm S K i)⟦t⟧ ⟶ K', g = 0 := by
  let : (S.componentLowerShriekDerived ⦋i⦌).CommShift ℤ := by
    dsimp only [componentLowerShriekDerived]
    infer_instance
  refine hom_eq_zero_of_iso
    ((shiftFunctor (DerivedCategory (Sheaf S.totalTopology Ab.{u})) t).mapIso
      (integerResolutionTensorTermIso S K hK i)) (Iso.refl K') ?_
  exact hom_eq_zero_of_shifted_leftAdjoint (S.componentLowerShriekDerivedAdjunction ⦋i⦌)
    ((derivedComponent S ⦋i⦌).obj K) t
    (((S.componentLowerShriekDerived ⦋i⦌).commShiftIso t).symm.app _) h

/-- **A map `X₀ ⟶ K` followed by a map `K ⟶ K'` whose degree-zero restriction vanishes is
zero**, for a cartesian `K`: the term `X₀` is `g_{0!}K₀` by Stacks 0D9E, and the transpose of the
composite along `g_{0!} ⊣ g_0^{-1}` factors through the degree-zero restriction of the second
map. -/
theorem comp_eq_zero_of_derivedComponent_map_eq_zero (hK : IsCartesianDerived S K)
    (a : integerResolutionTensorTerm S K 0 ⟶ K) (b : K ⟶ K')
    (hb : (derivedComponent S ⦋0⦌).map b = 0) : a ≫ b = 0 := by
  refine zero_of_epi_comp (integerResolutionTensorTermIso S K hK 0).inv ?_
  exact (Category.assoc _ _ _).symm.trans
    (comp_eq_zero_of_leftAdjoint (S.componentLowerShriekDerivedAdjunction ⦋0⦌)
      ((integerResolutionTensorTermIso S K hK 0).inv ≫ a) hb)

/-- **Stacks 0D9J.** In the simplicial-site situation of Stacks 09WE, let `K` and `K'` be objects
of `D(𝒞_total)` with `K` cartesian, and suppose that every morphism `Kᵢ[i] ⟶ K'ᵢ` vanishes for
`i > 0` and that every morphism `Kᵢ[i + 1] ⟶ K'ᵢ` vanishes for `i ≥ 0`. Then a map `K ⟶ K'`
inducing the zero map `K₀ ⟶ K'₀` is zero.

The proof is the source's. Stacks 0D9I presents `K` as the derived colimit of the system
`Yₙ[n]`, whose successive quotients are the shifted terms `Xₙ[n]`; Stacks 0D9E identifies `Xₙ`
with `g_{n!}Kₙ`, which turns the two vanishing hypotheses into the vanishing of the groups
`Hom(Xᵢ[t], K')` the induction consumes. -/
@[stacks 0D9J]
theorem eq_zero_of_derivedComponent_zero
    (hK : IsCartesianDerived S K)
    (hHom : ∀ i : ℕ, 0 < i →
      ∀ g : ((derivedComponent S ⦋i⦌).obj K)⟦(i : ℤ)⟧ ⟶ (derivedComponent S ⦋i⦌).obj K', g = 0)
    (hHomSucc : ∀ i : ℕ, ∀ g : ((derivedComponent S ⦋i⦌).obj K)⟦((i + 1 : ℕ) : ℤ)⟧ ⟶
      (derivedComponent S ⦋i⦌).obj K', g = 0)
    (f : K ⟶ K') (hf : (derivedComponent S ⦋0⦌).map f = 0) :
    f = 0 := by
  refine eq_zero_of_isHomotopyColimit_mapTruncTowerSystem (integerResolutionComplex S)
    (integerDerivedTensorRight S K)
    (isHomotopyColimit_derivedTensorIntegerResolutionSystem S K)
    (fun i hi => hom_integerResolutionTensorTerm_eq_zero S K K' hK i (i : ℤ) (hHom i hi))
    (fun i => ?_)
    (fun c => comp_eq_zero_of_derivedComponent_map_eq_zero S K K' hK c f hf)
  exact fun g => eq_zero_of_shift_eq' (by push_cast; ring)
    (hom_integerResolutionTensorTerm_eq_zero S K K' hK i ((i + 1 : ℕ) : ℤ) (hHomSucc i)) g

end CategoryTheory.SimplicialSiteSituation

end

module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Local annihilation of a torsion sheaf with finitely generated local values

Let `(C, J)` be a site and let `F` be a torsion abelian sheaf on it, i.e. one all of whose local
sections are locally annihilated by a positive integer
(`Stacks.Torsion.torsionSheafProperty`). The integer there is allowed to depend on the section
*and* on the arrow of the covering sieve along which the section is restricted. The invariant
`Stacks.ConstantSheaf.IsLocallyAnnihilated`, which is what the reduction of Tag 093U (2) to Tag
093U (3) consumes, asks for much more: a covering family on each member of which a *single*
positive integer annihilates the whole restriction of `F`.

This file proves that the second follows from the first as soon as `F`, read as a sheaf of
`ℤ`-modules, is locally constant of finite type
(`Stacks.ConstantSheaf.isLocallyAnnihilated_of_torsionSheafProperty`). Together with
`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf` this
makes local annihilation a consequence of torsion plus finite type, so that it need not be
carried as a separate hypothesis.

## Main results

* `Stacks.ConstantSheaf.exists_covering_nsmul_id_zero_of_constant_fg`: the uniformity step. Over
  an object where `F` is isomorphic to the constant sheaf on a finitely generated abelian group
  there is a covering sieve each of whose arrows carries a single positive integer annihilating
  the restriction of `F`.
* `Stacks.ConstantSheaf.isLocallyAnnihilated_of_torsionSheafProperty`: a torsion abelian sheaf
  which is locally constant of finite type over `ℤ` is locally annihilated.

## Implementation notes

**Where the uniformity comes from.** The trivialization `A̲ ≅ F|_{C/Y}` over an object `Y` turns
each element of `A` into a section of `F` over `Y`
(`Stacks.ConstantSheaf.trivSectionHom`), and the torsion hypothesis provides a covering sieve of
`Y` for each of them. Finite generation of `A` makes a *finite* family of sections suffice, so a
finite intersection of covering sieves — still covering — serves all of them at once, and the
product of the finitely many integers is a single annihilator of the image of `A` in the sections
over any member of that intersection. The elements of `A` annihilated by a fixed integer after
restriction form a subgroup, so killing the generators kills all of `A`.

**Why that is enough.** Annihilation of the whole restricted sheaf, not just of the sections
coming from `A`, is then automatic: morphisms out of a constant sheaf on a site with a terminal
object are, by the constant sheaf adjunction, determined by their composite with the canonical map
out of the value (`Stacks.ConstantSheaf.eq_zero_of_constantSheafUnitApp_comp`). Applying this to
`n • 𝟙` precomposed with the trivialization reduces annihilation of the identity of `F|_{C/V}` to
annihilation of the canonical sections. In particular the canonical map `A ⟶ Γ(V, A̲)` is never
required to be injective, and the degenerate objects covered by the empty sieve need no separate
treatment.

**The trivialization over a smaller object.** The trivialization used over a member `V ⟶ Y` of the
covering sieve is the one restricted from `Y`
(`Stacks.ConstantSheaf.restrictConstantIso`), and the section of `F` over `V` it cuts out is the
restriction of the section over `Y` (`Stacks.ConstantSheaf.trivSectionHom_restrictConstantIso`).
These are the arbitrary-value-category analogues of `Stacks.ConstantSheaf.restrictTrivIso` and
`Stacks.ConstantSheaf.trivSection_restrictTrivIso`, which are stated for sheaves of modules; the
ingredient that makes the comparison work, `Stacks.ConstantSheaf.mapPullbackConstantSheafApp`
together with its compatibility
`Stacks.ConstantSheaf.constantUnit_mapPullbackConstantSheafApp` with the canonical map out of the
constant presheaf, is already available for an arbitrary value category.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ConstantSheaf

/-! ### Morphisms out of a constant sheaf -/

section ConstantHom

variable {D : Type*} [Category* D] (K : GrothendieckTopology D)
  (A : Type*) [Category A] [HasWeakSheafify K A]

/-- The canonical map from an object of the value category to the sections over `V` of the
constant sheaf it generates: the component at `V` of the sheafification unit of the constant
presheaf. This is `Stacks.ConstantSheaf.constantUnitApp` with an arbitrary value category in
place of a category of modules. -/
abbrev constantSheafUnitApp (M : A) (V : Dᵒᵖ) :
    M ⟶ ((constantSheaf K A).obj M).obj.obj V :=
  (toSheafify K ((Functor.const Dᵒᵖ).obj M)).app V

variable [Preadditive A]

omit [HasWeakSheafify K A] in
/-- A multiple of a morphism of sheaves is computed on sections. -/
theorem nsmul_hom_app {P Q : Sheaf K A} (n : ℕ) (φ : P ⟶ Q) (V : Dᵒᵖ) :
    (n • φ).hom.app V = n • φ.hom.app V := by
  induction n with
  | zero => simp
  | succ k ih => rw [succ_nsmul, succ_nsmul, Sheaf.Hom.add_app, ih]

/-- **A morphism out of a constant sheaf which kills the canonical section is zero.** The
constant sheaf adjunction on a site with a terminal object `T` identifies morphisms `M̲ ⟶ G` with
morphisms `M ⟶ Γ(T, G)`, by composition with the canonical map out of `M`; a morphism whose
composite with that map vanishes is therefore zero. -/
theorem eq_zero_of_constantSheafUnitApp_comp {T : D} (hT : IsTerminal T) (M : A) (G : Sheaf K A)
    (φ : (constantSheaf K A).obj M ⟶ G)
    (h : constantSheafUnitApp K A M (op T) ≫ φ.hom.app (op T) = 0) : φ = 0 := by
  refine ((constantSheafAdj K A hT).homEquiv M G).injective ?_
  rw [constantSheafAdj_homEquiv_apply K A hT M G φ,
    constantSheafAdj_homEquiv_apply K A hT M G 0]
  exact h.trans comp_zero.symm

/-- **An integer annihilating the canonical section annihilates a constant sheaf.** If `G` is
isomorphic to the constant sheaf on `M` over a site with a terminal object `T`, and `n`
annihilates the section of `G` over `T` that the isomorphism attaches to `M`, then `n`
annihilates the identity of `G`. -/
theorem nsmul_id_zero_of_nsmul_constantSheafUnitApp {T : D} (hT : IsTerminal T) (M : A)
    (G : Sheaf K A) (β : (constantSheaf K A).obj M ≅ G) (n : ℕ)
    (h : n • (constantSheafUnitApp K A M (op T) ≫ β.hom.hom.app (op T)) = 0) :
    n • 𝟙 G = 0 := by
  have hz : β.hom ≫ (n • 𝟙 G) = 0 := by
    refine eq_zero_of_constantSheafUnitApp_comp K A hT M G _ ?_
    simpa only [nsmul_hom_app, Category.comp_id, Preadditive.comp_nsmul] using h
  exact (cancel_epi β.hom).1 (hz.trans comp_zero.symm)

end ConstantHom

/-! ### Sections cut out by a trivialization, and its restriction -/

section Restrict

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (A : Type*) [Category A]
  {F : Sheaf J A}

/-- **The section cut out by a trivialization.** A trivialization `α` of `F` over `U` by the
constant sheaf on `M` sends an element of `M` to a section of `F` over `U`: take the canonical
image in the sections of `M̲` at the terminal object of `C/U` and apply `α`. This is
`Stacks.ConstantSheaf.trivSection` for an arbitrary value category, read at the terminal object
and as a morphism rather than on elements. -/
abbrev trivSectionHom {U : C} (M : A) [HasWeakSheafify (J.over U) A]
    (α : (constantSheaf (J.over U) A).obj M ≅ (J.overPullback A U).obj F) :
    M ⟶ F.obj.obj (op U) :=
  constantSheafUnitApp (J.over U) A M (op (Over.mk (𝟙 U))) ≫
    α.hom.hom.app (op (Over.mk (𝟙 U)))

/-- The sections cut out by a trivialization over `U` are the restrictions of the one over the
terminal object of `C/U`. -/
theorem constantSheafUnitApp_comp_app {U : C} (M : A) [HasWeakSheafify (J.over U) A]
    (α : (constantSheaf (J.over U) A).obj M ≅ (J.overPullback A U).obj F) (W : Over U) :
    constantSheafUnitApp (J.over U) A M (op W) ≫ α.hom.hom.app (op W) =
      trivSectionHom J A M α ≫ F.obj.map W.hom.op := by
  let g : W ⟶ Over.mk (𝟙 U) := Over.homMk W.hom (Category.comp_id _)
  have hu : constantSheafUnitApp (J.over U) A M (op W) =
      constantSheafUnitApp (J.over U) A M (op (Over.mk (𝟙 U))) ≫
        ((constantSheaf (J.over U) A).obj M).obj.map g.op :=
    (Category.id_comp _).symm.trans
      ((toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj M)).naturality g.op)
  rw [hu, Category.assoc, α.hom.hom.naturality g.op, ← Category.assoc]
  rfl

/-- **A trivialization restricted to an object lying over the one it is given on.** The result
type is ascribed so that the target is spelled `j_Z^{-1} F` rather than `j_q^{-1} j_U^{-1} F`; the
two are definitionally equal by `Stacks.ConstantSheaf.overPullback_eq_comp`. This is
`Stacks.ConstantSheaf.restrictTrivIso` with an arbitrary value category in place of a category of
modules. -/
def restrictConstantIso {U Z : C} (q : Z ⟶ U) (M : A)
    [HasWeakSheafify (J.over U) A] [HasWeakSheafify (J.over Z) A]
    [∀ (G : (Over Z)ᵒᵖ ⥤ A), (Over.map q).op.HasPointwiseRightKanExtension G]
    (α : (constantSheaf (J.over U) A).obj M ≅ (J.overPullback A U).obj F) :
    (constantSheaf (J.over Z) A).obj M ≅ (J.overPullback A Z).obj F :=
  (mapPullbackConstantSheafApp J A q M).trans ((J.overMapPullback A q).mapIso α)

/-- **Restricting a trivialization restricts the sections it cuts out.** The section of `F` over
`Z` attached to an element of `M` by the restricted trivialization is the restriction along
`q : Z ⟶ U` of the section over `U` attached to it by the original one. -/
theorem trivSectionHom_restrictConstantIso {U Z : C} (q : Z ⟶ U) (M : A)
    [HasWeakSheafify (J.over U) A] [HasWeakSheafify (J.over Z) A]
    [∀ (G : (Over Z)ᵒᵖ ⥤ A), (Over.map q).op.HasPointwiseRightKanExtension G]
    (α : (constantSheaf (J.over U) A).obj M ≅ (J.overPullback A U).obj F) :
    constantSheafUnitApp (J.over Z) A M (op (Over.mk (𝟙 Z))) ≫
        (restrictConstantIso J A q M α).hom.hom.app (op (Over.mk (𝟙 Z))) =
      trivSectionHom J A M α ≫ F.obj.map q.op := by
  have h := constantUnit_mapPullbackConstantSheafApp J A q M (op (Over.mk (𝟙 Z)))
  have hstep : constantSheafUnitApp (J.over Z) A M (op (Over.mk (𝟙 Z))) ≫
      (restrictConstantIso J A q M α).hom.hom.app (op (Over.mk (𝟙 Z))) =
      constantSheafUnitApp (J.over U) A M (op ((Over.map q).obj (Over.mk (𝟙 Z)))) ≫
        α.hom.hom.app (op ((Over.map q).obj (Over.mk (𝟙 Z)))) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun x => x ≫ α.hom.hom.app (op ((Over.map q).obj (Over.mk (𝟙 Z))))) h)
  have hw : ((Over.map q).obj (Over.mk (𝟙 Z))).hom = q := by simp
  rw [hstep, constantSheafUnitApp_comp_app J A M α ((Over.map q).obj (Over.mk (𝟙 Z))), hw]

end Restrict

/-! ### Torsion plus finite type gives local annihilation -/

section Main

universe v u w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

attribute [local instance] hasSheafify_addCommGrp hasSheafCompose_intCoefficients
  preservesSheafification_intCoefficients hasSheafCompose_forget₂_int
  preservesSheafification_forget₂_int

/-- **The uniformity step.** Over an object `Y` where the torsion abelian sheaf `F` is isomorphic
to the constant sheaf on a finitely generated abelian group there is a covering sieve of `Y` such
that the restriction of `F` to each of its members is annihilated by a single positive integer.

The integers supplied by the torsion hypothesis depend on the section and on the arrow; finite
generation of the local value is what collapses that dependence to a finite intersection of
covering sieves and a product of finitely many integers. -/
theorem exists_covering_nsmul_id_zero_of_constant_fg
    (F : Sheaf J AddCommGrpCat.{max u v w})
    (hTor : Stacks.Torsion.torsionSheafProperty J F) {Y : C}
    (A : AddCommGrpCat.{max u v w}) (hA : AddGroup.FG A)
    (α : (constantSheaf (J.over Y) AddCommGrpCat.{max u v w}).obj A ≅
      (J.overPullback AddCommGrpCat.{max u v w} Y).obj F) :
    ∃ R : Sieve Y, R ∈ J Y ∧ ∀ (V : C) (b : V ⟶ Y), R b →
      ∃ n : ℕ, n ≠ 0 ∧ n • 𝟙 ((J.overPullback AddCommGrpCat.{max u v w} V).obj F) = 0 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset A, AddSubgroup.closure (S : Set A) = ⊤ :=
    let ⟨_, S, _, hS⟩ := AddGroup.fg_iff'.1 hA; ⟨S, hS⟩
  have htor : ∀ m : A, ∃ R : Sieve Y, R ∈ J Y ∧ ∀ (V : C) (g : V ⟶ Y), R g →
      ∃ k : ℕ, 0 < k ∧
        k • (F.obj.map g.op (trivSectionHom J AddCommGrpCat.{max u v w} A α m)) = 0 :=
    fun m => hTor Y (trivSectionHom J AddCommGrpCat.{max u v w} A α m)
  choose R hR hRkill using htor
  refine ⟨S.inf R, finset_inf_covering J S R (fun m _ => hR m), fun V b hb => ?_⟩
  have hk : ∀ m ∈ S, ∃ k : ℕ, 0 < k ∧
      k • (F.obj.map b.op (trivSectionHom J AddCommGrpCat.{max u v w} A α m)) = 0 :=
    fun m hm => hRkill m V b ((Finset.inf_le hm : S.inf R ≤ R m) b hb)
  choose! k hk0 hkz using hk
  refine ⟨∏ m ∈ S, k m, Finset.prod_ne_zero_iff.2 fun m hm => (hk0 m hm).ne', ?_⟩
  have hall : ∀ m : A, (∏ m ∈ S, k m) •
      (F.obj.map b.op (trivSectionHom J AddCommGrpCat.{max u v w} A α m)) = 0 := by
    intro m
    have hmem : m ∈ AddSubgroup.closure (S : Set A) := by simp [hS]
    induction hmem using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k hx
      rw [hc, mul_comm, mul_smul, hkz x hx, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, smul_add, hx, hy]
    | neg x _ hx => simp [map_neg, smul_neg, hx]
  refine nsmul_id_zero_of_nsmul_constantSheafUnitApp (J.over V) AddCommGrpCat.{max u v w}
    (Over.mkIdTerminal (X := V)) A _
    (restrictConstantIso J AddCommGrpCat.{max u v w} b A α) _ ?_
  rw [trivSectionHom_restrictConstantIso J AddCommGrpCat.{max u v w} b A α]
  ext m
  exact hall m

/-- **A torsion abelian sheaf which is locally constant of finite type is locally annihilated.**
Every object of the site has a covering family on each member of which a single positive integer
annihilates the whole restriction of `F`.

This is the missing input of
`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf`: the
annihilators provided by torsion depend on the section and on the arrow, and finite generation of
the local values is what makes them uniform. -/
theorem isLocallyAnnihilated_of_torsionSheafProperty
    (F : Sheaf J AddCommGrpCat.{max u v w})
    (hTor : Stacks.Torsion.torsionSheafProperty J F)
    (hFin : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J ℤ ((intSheaf.{v, u, w} J).obj F)) :
    IsLocallyAnnihilated.{v, u, w} J F := by
  classical
  intro U
  obtain ⟨I, X, f, hf, hX⟩ :=
    exists_cover_fg_of_isFiniteTypeLocallyConstantModuleSheaf J F hFin U
  have hstep : ∀ i : I, ∃ R : Sieve (X i), R ∈ J (X i) ∧ ∀ (V : C) (b : V ⟶ X i), R b →
      ∃ n : ℕ, n ≠ 0 ∧ n • 𝟙 ((J.overPullback AddCommGrpCat.{max u v w} V).obj F) = 0 := by
    intro i
    obtain ⟨A, hA, ⟨α⟩⟩ := hX i
    exact exists_covering_nsmul_id_zero_of_constant_fg J F hTor A hA α
  choose R hR hRkill using hstep
  let T : Sieve U :=
    { arrows := fun V h => ∃ (i : I) (b : V ⟶ X i), R i b ∧ h = b ≫ f i
      downward_closed := by
        rintro V W h ⟨i, b, hb, rfl⟩ g
        exact ⟨i, g ≫ b, (R i).downward_closed hb g, by simp⟩ }
  have hT : T ∈ J U := by
    refine J.transitive hf T fun V h hh => ?_
    obtain ⟨i, b, rfl⟩ := Sieve.ofArrows.exists hh
    refine J.superset_covering (fun W g hg => ?_) (J.pullback_stable b (hR i))
    exact ⟨i, g ≫ b, hg, by simp⟩
  obtain ⟨L, Z, q, hq⟩ := T.exists_eq_ofArrows
  refine ⟨L, Z, q, ?_, fun l => ?_⟩
  · rwa [← hq]
  · have hmem : T.arrows (q l) := by
      rw [hq]
      exact Sieve.ofArrows_mk Z q l
    obtain ⟨i, b, hb, -⟩ := hmem
    exact hRkill i (Z l) b hb

end Main

end Stacks.ConstantSheaf

end

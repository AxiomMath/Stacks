module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.LocalAgreement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Shrink
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Surjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.Limits.EtaleChartDescent

/-!
# Sections of an étale sheaf over the limit of a cofiltered system of étale charts

Let `X` be a scheme, `F` a sheaf of sets on its small étale site, and let `(Uᵢ)` be a cofiltered
inverse system of quasi-compact and quasi-separated schemes étale over `X`, with affine
transition morphisms and limit `U = lim Uᵢ`, mapping to `X` by `π`. Every section of `F` over a
stage `Uᵢ` pulls back to a global section of `π⁻¹F` over `U`. This file proves that two sections
over a stage with the same pullback agree over a later stage. Together with the existence half,
this identifies `Γ(U, π⁻¹F)` with `colim_i F(Uᵢ)`, which is [Stacks, Tag 03Q9] for global
sections of sheaves of sets when `U` is the base change of `X` to a strict henselization.

## Main definitions

* `Stacks.EtaleCohomology.limitStageLift` — the morphism from the final object of the small étale
  site of `U` to the base change of `Uᵢ`, induced by the projection `U ⟶ Uᵢ`.
* `Stacks.EtaleCohomology.limitStagePullback` — the pullback of a section over `Uᵢ` to a global
  section of `π⁻¹F`.

## Main results

* `Stacks.EtaleCohomology.exists_eq_of_limitStagePullback_eq` — two sections over a stage with the
  same pullback to `U` agree over a later stage.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace Stacks.EtaleCohomology

section LanWitness

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- **Equality in the left Kan extension is witnessed over a single object, compatibly.** For a
morphism `k : V ⟶ W₀ ×_X Z` of the small étale site of `Z`, two sections of an étale sheaf over
`W₀` whose images under the unit of the left Kan extension agree after restriction along `k`
agree over some `W ⟶ W₀` through whose base change `k` factors. -/
theorem exists_map_eq_of_lan_eq {V : Z.Etale} {W₀ : X.Etale}
    (k : V ⟶ (smallEtaleBaseChange i).obj W₀)
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
    (a b : F.obj.obj (op W₀))
    (h : ((smallEtaleBaseChange i).op.lan.obj F.obj).map k.op
          (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W₀) a)
        = ((smallEtaleBaseChange i).op.lan.obj F.obj).map k.op
          (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W₀) b)) :
    ∃ (W : X.Etale) (q : W ⟶ W₀) (k' : V ⟶ (smallEtaleBaseChange i).obj W),
      k' ≫ (smallEtaleBaseChange i).map q = k ∧ F.obj.map q.op a = F.obj.map q.op b := by
  have hcolim := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((smallEtaleBaseChange i).op.lan.obj F.obj)
      ((smallEtaleBaseChange i).op.lanUnit.app F.obj) (op V)
  have hι : ∀ c : F.obj.obj (op W₀),
      ((Functor.LeftExtension.mk ((smallEtaleBaseChange i).op.lan.obj F.obj)
        ((smallEtaleBaseChange i).op.lanUnit.app F.obj)).coconeAt (op V)).ι.app
          (CostructuredArrow.mk k.op :
            CostructuredArrow (smallEtaleBaseChange i).op (op V)) c
        = ((smallEtaleBaseChange i).op.lan.obj F.obj).map k.op
            (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op W₀) c) := fun _ ↦ rfl
  obtain ⟨jj, φ, hφ⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (i := (CostructuredArrow.mk k.op :
      CostructuredArrow (smallEtaleBaseChange i).op (op V))) hcolim a b).mp
    (by rw [hι a, hι b]; exact h)
  refine ⟨jj.left.unop, φ.left.unop, jj.hom.unop, ?_, hφ⟩
  have hw := CostructuredArrow.w φ
  exact Quiver.Hom.op_inj hw

/-- Every point of `V` lies in the image of an arrow of a covering sieve of `V`. -/
private theorem exists_mem_sieve_of_mem_smallEtaleTopology {V : Z.Etale} {S : Sieve V}
    (hS : S ∈ Scheme.smallEtaleTopology Z V) (z : V.left) :
    ∃ (Y : Z.Etale) (p : Y ⟶ V) (v : Y.left), S.arrows p ∧ p.left.base v = z := by
  obtain ⟨α, Y, p, hEq⟩ := S.exists_eq_ofArrows
  obtain ⟨j, v, hv⟩ : ∃ j, z ∈ Set.range (p j).left :=
    Set.mem_iUnion.mp (((Scheme.ofArrows_mem_smallEtaleTopology_iff p).mp (hEq ▸ hS)) ▸
      Set.mem_univ z)
  exact ⟨Y j, p j, v, hEq ▸ (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, 𝟙 _, (Category.id_comp _).symm⟩,
    hv⟩

/-- **A section of an inverse image is, near each point, pulled back from the base over an
affine chart.** For a section `t` of `i⁻¹F` over `V₀` and a point `z` of `V₀`, there are an object
`V ⟶ V₀` of the small étale site of `Z` with affine source whose image contains `z`, an object `W`
of the small étale site of `X`, a morphism `k : V ⟶ W ×_X Z` and a section of `F` over `W` whose
pullback restricted along `k` is the restriction of `t` to `V`. -/
theorem exists_affine_local_rep (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
    {V₀ : Z.Etale} (t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op V₀))
    (z : V₀.left) :
    ∃ (V : Z.Etale) (a : V ⟶ V₀) (W : X.Etale) (k : V ⟶ (smallEtaleBaseChange i).obj W)
      (s₀ : F.obj.obj (op W)), IsAffine V.left ∧ z ∈ Set.range a.left.base ∧
        ((smallEtaleInverseImage.{u, v} i).obj F).obj.map a.op t =
          ((smallEtaleInverseImage.{u, v} i).obj F).obj.map k.op
            (smallEtaleSectionPullback.{u, v} i F W s₀) := by
  let L := (smallEtaleBaseChange i).op.lan.obj F.obj
  have hS : Presheaf.imageSieve (toSheafify (Scheme.smallEtaleTopology Z) L) t ∈
      Scheme.smallEtaleTopology Z V₀ := Presheaf.IsLocallySurjective.imageSieve_mem _
  obtain ⟨Y, p, v, ⟨x, hx⟩, hv⟩ := exists_mem_sieve_of_mem_smallEtaleTopology hS z
  obtain ⟨W, k, s₀, hk⟩ := exists_rep_lan_smallEtaleBaseChange i Y F x
  obtain ⟨_, ⟨B, hB, rfl⟩, hvB, -⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ v) isOpen_univ
  let ι := smallEtaleRestrictHom Y B
  have hrel : ((smallEtaleInverseImage.{u, v} i).obj F).obj.map p.op t =
      ((smallEtaleInverseImage.{u, v} i).obj F).obj.map k.op
        (smallEtaleSectionPullback.{u, v} i F W s₀) := by
    rw [map_smallEtaleSectionPullback, hk]
    exact hx.symm
  refine ⟨smallEtaleRestrict Y B, ι ≫ p, W, ι ≫ k, s₀, hB, ⟨⟨v, hvB⟩, hv⟩, ?_⟩
  rw [op_comp, FunctorToTypes.map_comp_apply, op_comp, FunctorToTypes.map_comp_apply, hrel]

end LanWitness

/-- Bookkeeping for `limitBaseChangeStageMap`, stated for plain schemes. -/
private lemma stage_cond {A B B' C D₁ D₂ : Scheme.{u}} (p₁ : A ⟶ B) (p₂ : A ⟶ C) (r : B ⟶ B')
    (ρ₁ : B ⟶ D₁) (ρ₂ : B' ⟶ D₂) (dh : D₁ ⟶ D₂) (c₁ : C ⟶ D₁) (c₂ : C ⟶ D₂)
    (hr : r ≫ ρ₂ = ρ₁ ≫ dh) (hp : p₁ ≫ ρ₁ = p₂ ≫ c₁) (hc : c₁ ≫ dh = c₂) :
    (p₁ ≫ r) ≫ ρ₂ = p₂ ≫ c₂ := by
  rw [Category.assoc, hr, ← Category.assoc, hp, Category.assoc, hc]

/-- In a cartesian square of schemes, a point of one factor whose image agrees with the image
of a point of the other factor is hit by the fibre product. -/
private lemma exists_preimage_snd_of_isPullback {P A B C : Scheme.{u}} {p₁ : P ⟶ A}
    {p₂ : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (sq : IsPullback p₁ p₂ f g) (a : A) (b : B)
    (e : f.base a = g.base b) : ∃ y : P, p₂.base y = b := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback a b e
  refine ⟨sq.isoPullback.inv.base z, ?_⟩
  have he : sq.isoPullback.inv ≫ p₂ = pullback.snd f g := by
    rw [Iso.inv_comp_eq]
    exact sq.isoPullback_hom_snd.symm
  rw [← Scheme.Hom.comp_apply, he]
  exact hz

/-- The objects of the small étale site over `Q` on which the sections `s` and `s'` agree. -/
private abbrev AgreeingMap {X : Scheme.{u}}
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) {Q : X.Etale}
    (s s' : F.obj.obj (op Q)) :=
  {wq : Σ W : X.Etale, W ⟶ Q // F.obj.map wq.2.op s = F.obj.map wq.2.op s'}

/-- The union of the images of the objects over `Q` on which `s` and `s'` agree. -/
private def agreementLocus {X : Scheme.{u}}
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) {Q : X.Etale}
    (s s' : F.obj.obj (op Q)) : Set Q.left :=
  ⋃ b : AgreeingMap F s s', Set.range b.1.2.left.base

private theorem isOpen_agreementLocus {X : Scheme.{u}}
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) {Q : X.Etale}
    (s s' : F.obj.obj (op Q)) : IsOpen (agreementLocus F s s') :=
  isOpen_iUnion fun b => b.1.2.left.isOpenMap.isOpen_range

/-- If two sections of `F` over `Q` have the same pullback after restriction along a morphism
`lam` to the base change of `Q`, every point of the image of `lam` in `Q` lies in the agreement
locus of the two sections. -/
private theorem fst_mem_agreementLocus {Z X : Scheme.{u}} (π : Z ⟶ X)
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) {Q : X.Etale} {T : Z.Etale}
    (lam : T ⟶ (smallEtaleBaseChange π).obj Q) (s s' : F.obj.obj (op Q))
    (h : ((smallEtaleInverseImage.{u, v} π).obj F).obj.map lam.op
        (smallEtaleSectionPullback.{u, v} π F Q s) =
      ((smallEtaleInverseImage.{u, v} π).obj F).obj.map lam.op
        (smallEtaleSectionPullback.{u, v} π F Q s')) (z : T.left) :
    (lam.left ≫ pullback.fst Q.hom π).base z ∈ agreementLocus F s s' := by
  let L := (smallEtaleBaseChange π).op.lan.obj F.obj
  let η := (smallEtaleBaseChange π).op.lanUnit.app F.obj
  have h' : (toSheafify (Scheme.smallEtaleTopology Z) L).app (op T)
        (L.map lam.op (η.app (op Q) s)) =
      (toSheafify (Scheme.smallEtaleTopology Z) L).app (op T)
        (L.map lam.op (η.app (op Q) s')) :=
    (map_smallEtaleSectionPullback.{u, v} π F lam s).symm.trans
      (h.trans (map_smallEtaleSectionPullback.{u, v} π F lam s'))
  obtain ⟨Y, p, v, hin, hv⟩ :=
    exists_mem_sieve_of_mem_smallEtaleTopology (equalizerSieve_mem_of_toSheafify_eq L _ _ h') z
  have hmem' : L.map (p ≫ lam).op (η.app (op Q) s) = L.map (p ≫ lam).op (η.app (op Q) s') :=
    ((Functor.map_comp_apply _ lam.op p.op _).trans hin).trans
      (Functor.map_comp_apply _ lam.op p.op _).symm
  obtain ⟨W, q, k', hk', hq⟩ := exists_map_eq_of_lan_eq π (p ≫ lam) F s s' hmem'
  refine Set.mem_iUnion.mpr ⟨⟨⟨W, q⟩, hq⟩, (pullback.fst W.hom π).base (k'.left.base v), ?_⟩
  have hkl0 := congrArg (fun m => m.left ≫ pullback.fst Q.hom π) hk'
  have hkl : k'.left ≫ ((smallEtaleBaseChange π).map q).left ≫ pullback.fst Q.hom π =
      p.left ≫ lam.left ≫ pullback.fst Q.hom π :=
    (Category.assoc _ _ _).symm.trans (hkl0.trans (Category.assoc _ _ _))
  have h2 : k'.left ≫ pullback.fst W.hom π ≫ q.left = p.left ≫ lam.left ≫ pullback.fst Q.hom π :=
    (congrArg (k'.left ≫ ·) (smallEtaleBaseChange_map_left_fst π q).symm).trans hkl
  have h3 := congrArg (fun m => m.base v) h2
  simp only [Scheme.Hom.comp_apply] at h3 ⊢
  rw [← hv]
  exact h3

/-- If the image of `g` lies in the agreement locus of two sections of `F` over `Q`, then the
sections agree after restriction along `g`. -/
private theorem map_eq_of_range_subset_agreementLocus {X : Scheme.{u}}
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) {Q Q' : X.Etale}
    (g : Q' ⟶ Q) (s s' : F.obj.obj (op Q))
    (h : Set.range g.left.base ⊆ agreementLocus F s s') :
    F.obj.map g.op s = F.obj.map g.op s' := by
  have hcov : Sieve.ofArrows (fun b : AgreeingMap F s s' => pullback b.1.2 g)
      (fun b => pullback.snd b.1.2 g) ∈ Scheme.smallEtaleTopology X Q' := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨b, w, hw⟩ := Set.mem_iUnion.mp (h ⟨x, rfl⟩)
    obtain ⟨y, hy⟩ := exists_preimage_snd_of_isPullback ((IsPullback.of_hasPullback b.1.2
      g).map (Scheme.Etale.forget X ⋙ Over.forget X)) w x hw
    exact Set.mem_iUnion.mpr ⟨b, y, hy⟩
  refine (((isSheaf_iff_isSheaf_of_type _ _).1 F.property) _ hcov).isSeparatedFor.ext ?_
  rintro T f ⟨T', k, _, ⟨b⟩, rfl⟩
  have key : ∀ t, F.obj.map (pullback.snd b.1.2 g).op (F.obj.map g.op t) =
      F.obj.map (pullback.fst b.1.2 g).op (F.obj.map b.1.2.op t) := by
    intro t
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      pullback.condition]
  simp only [op_comp, Functor.map_comp_apply, key, b.2]

/-- Two morphisms into a base change with the same first projection agree, so a square of
morphisms to base changes commutes as soon as its first projections do. -/
private theorem comp_map_eq_comp_of_left_fst {Z X : Scheme.{u}} (π : Z ⟶ X) {P₁ P₂ : Z.Etale}
    {Q₁ Q₂ : X.Etale} (r : Q₁ ⟶ Q₂) (m : P₁ ⟶ P₂) (l₁ : P₁ ⟶ (smallEtaleBaseChange π).obj Q₁)
    (l₂ : P₂ ⟶ (smallEtaleBaseChange π).obj Q₂) {f₁ : P₁.left ⟶ Q₁.left} {f₂ : P₂.left ⟶ Q₂.left}
    (h₁ : l₁.left ≫ pullback.fst Q₁.hom π = f₁) (h₂ : l₂.left ≫ pullback.fst Q₂.hom π = f₂)
    (hm : m.left ≫ f₂ = f₁ ≫ r.left) : l₁ ≫ (smallEtaleBaseChange π).map r = m ≫ l₂ := by
  refine smallEtaleBaseChange_hom_ext π ?_
  change (l₁.left ≫ ((smallEtaleBaseChange π).map r).left) ≫ _ = (m.left ≫ l₂.left) ≫ _
  erw [Category.assoc, Category.assoc, smallEtaleBaseChange_map_left_fst, ← Category.assoc, h₁,
    h₂, hm]

/-- **A common refinement in a cofiltered category.** Finitely many morphisms `eₖ : jₖ ⟶ i` admit
a common source `j₀` with morphisms `fₖ : j₀ ⟶ jₖ` all of whose composites with the `eₖ` agree. -/
theorem exists_common_refinement {J : Type*} [Category* J] [IsCofiltered J] {ι : Type*} [Finite ι]
    (i : J) (j : ι → J) (e : ∀ k, j k ⟶ i) :
    ∃ (j₀ : J) (g : j₀ ⟶ i) (f : ∀ k, j₀ ⟶ j k), ∀ k, f k ≫ e k = g := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  suffices H : ∀ S : Finset ι, ∃ (j₀ : J) (g : j₀ ⟶ i), ∀ k ∈ S, ∃ f : j₀ ⟶ j k, f ≫ e k = g by
    obtain ⟨j₀, g, hg⟩ := H Finset.univ
    choose f hf using fun k => hg k (Finset.mem_univ k)
    exact ⟨j₀, g, f, hf⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨i, 𝟙 i, fun k hk => absurd hk (Finset.notMem_empty k)⟩
  | @insert a S _ ih =>
    obtain ⟨j₀, g, hg⟩ := ih
    obtain ⟨j₁, p, q, -⟩ := IsCofilteredOrEmpty.cone_objs j₀ (j a)
    obtain ⟨j₂, h, hh⟩ := IsCofilteredOrEmpty.cone_maps (p ≫ g) (q ≫ e a)
    refine ⟨j₂, h ≫ p ≫ g, fun k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact ⟨h ≫ q, by rw [Category.assoc, ← hh]⟩
    · obtain ⟨f, hf⟩ := hg k hk
      exact ⟨h ≫ p ≫ f, by rw [Category.assoc, Category.assoc, hf]⟩

section Limit

variable {X : Scheme.{u}} {I : Type u} [SmallCategory I] (D : I ⥤ X.Etale)
  (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X)) (π : c.pt ⟶ X)
  (hπ : ∀ i, c.π.app i ≫ (D.obj i).hom = π)
  (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))

/-- The morphism from the final object `U = U / U` of the small étale site of the limit `U` to
the base change of the stage `Uᵢ`, induced by the projection `U ⟶ Uᵢ`. -/
def limitStageLift (i : I) :
    Scheme.Etale.mk (𝟙 c.pt) ⟶ (smallEtaleBaseChange π).obj (D.obj i) :=
  smallEtaleBaseChangeLift π (D.obj i) (c.π.app i) (hπ i)

/-- The morphism `limitStageLift D c π hπ i` composed with the first projection `Uᵢ ×_X U ⟶ Uᵢ`
is the projection `U ⟶ Uᵢ`. -/
@[reassoc (attr := simp)]
theorem limitStageLift_left_fst (i : I) :
    (limitStageLift D c π hπ i).left ≫ pullback.fst (D.obj i).hom π = c.π.app i :=
  pullback.lift_fst _ _ _

/-- The pullback of a section of `F` over the stage `Uᵢ` to a global section of `π⁻¹F` over the
limit. -/
def limitStagePullback (i : I) (s : F.obj.obj (op (D.obj i))) :
    ((smallEtaleInverseImage.{u, v} π).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))) :=
  ((smallEtaleInverseImage.{u, v} π).obj F).obj.map (limitStageLift D c π hπ i).op
    (smallEtaleSectionPullback.{u, v} π F (D.obj i) s)

/-- **An open set containing every preimage of the limit contains the preimages of a later
stage.** If `ρ : Q ⟶ Uᵢ` with `Q` quasi-compact and every point of `Q` over a point in the image
of `U` lies in the open set `E`, then for some `j ⟶ i` every point of `Q` over a point of `Uⱼ`
lies in `E` (Stacks 05F3). -/
private theorem exists_stage_forall_mem_of_isOpen [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e).left] (i : I) {Q : Scheme.{u}}
    [CompactSpace Q] (ρ : Q ⟶ (D.obj i).left) {E : Set Q} (hE : IsOpen E)
    (h : ∀ (v : c.pt) (q : Q), ρ.base q = (c.π.app i).base v → q ∈ E) :
    ∃ (j : I) (g : j ⟶ i), ∀ (y : (D.obj j).left) (q : Q),
      ρ.base q = (D.map g).left.base y → q ∈ E := by
  let Ii := Scheme.IdealSheafData.vanishingIdeal (⟨Eᶜ, hE.isClosed_compl⟩ :
    TopologicalSpace.Closeds Q)
  have hrange : Set.range Ii.subschemeι.base = Eᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : CompactSpace Ii.subscheme := QuasiCompact.compactSpace_of_compactSpace Ii.subschemeι
  have hT : IsEmpty (pullback (c.π.app i : c.pt ⟶ (D.obj i).left) (Ii.subschemeι ≫ ρ) :
      Scheme.{u}) := by
    refine ⟨fun x => ?_⟩
    have := congrArg (fun m => m.base x) (pullback.condition (f :=
      (c.π.app i : c.pt ⟶ (D.obj i).left)) (g := Ii.subschemeι ≫ ρ))
    simp only [Scheme.Hom.comp_apply] at this
    exact (hrange ▸ Set.mem_range_self _ : _ ∈ Eᶜ) (h _ _ this.symm)
  have : ∀ {a b : I} (e : a ⟶ b),
      IsAffineHom ((D ⋙ Scheme.Etale.forget X ⋙ Over.forget X).map e) :=
    fun e => inferInstanceAs (IsAffineHom (D.map e).left)
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  obtain ⟨j, g, hg⟩ := exists_isEmpty_pullback_map_of_isEmpty_pullback_π_app
    (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X) c hc i (Ii.subschemeι ≫ ρ) hT
  refine ⟨j, g, fun y q hq => ?_⟩
  by_contra hqE
  obtain ⟨b, hb⟩ : q ∈ Set.range Ii.subschemeι.base := hrange ▸ hqE
  obtain ⟨y', -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (D.map g).left) y b
    (by rw [Scheme.Hom.comp_apply, hb, hq])
  exact hg.false y'

/-- **Two sections over a stage with the same pullback to the limit agree over a later stage.**
Equality of the pullbacks is witnessed locally in the left Kan extension computing the inverse
image, hence over objects `W ⟶ Uᵢ` of the small étale site of `X` whose images cover the image of
`U` in `Uᵢ`; the complement of that union is a closed subset of `Uᵢ` missing the image of the
limit, so it misses the image of a later stage `Uⱼ` (Stacks 05F3), and the two sections agree on
the covering of `Uⱼ` by the base changes of the `W`. -/
theorem exists_eq_of_limitStagePullback_eq [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e).left]
    [∀ i, CompactSpace (D.obj i).left] (i : I) (s s' : F.obj.obj (op (D.obj i)))
    (h : limitStagePullback D c π hπ F i s = limitStagePullback D c π hπ F i s') :
    ∃ (j : I) (e : j ⟶ i), F.obj.map (D.map e).op s = F.obj.map (D.map e).op s' := by
  have hlimE : ∀ v : c.pt, (c.π.app i : c.pt ⟶ (D.obj i).left).base v ∈ agreementLocus F s s' :=
    fun v => by
      have := fst_mem_agreementLocus π F (limitStageLift D c π hπ i) s s' h v
      rwa [limitStageLift_left_fst] at this
  obtain ⟨j, g, hg⟩ := exists_stage_forall_mem_of_isOpen D c hc i (𝟙 (D.obj i).left)
    (isOpen_agreementLocus F s s') fun v q hq => by
      rw [show q = (c.π.app i).base v from hq]
      exact hlimE v
  exact ⟨j, g, map_eq_of_range_subset_agreementLocus F (D.map g) s s'
    (by rintro _ ⟨y, rfl⟩; exact hg y _ rfl)⟩

/-- The base change to the limit of an object `Q` of the small étale site of `X` lying over the
stage `Uᵢ`, as an object of the small étale site of the limit: `Q ×_{Uᵢ} U`. -/
abbrev limitBaseChangeObj (i : I) {Q : X.Etale} (ρ : Q ⟶ D.obj i) : c.pt.Etale :=
  haveI := Etale.instSndScheme ρ.left (c.π.app i : c.pt ⟶ (D.obj i).left)
  Scheme.Etale.mk (pullback.snd ρ.left (c.π.app i : c.pt ⟶ (D.obj i).left))

include hπ in
/-- The morphism `Q ×_{Uᵢ} U ⟶ Q ×_X U` of the small étale site of the limit. -/
def limitBaseChangeLift (i : I) {Q : X.Etale} (ρ : Q ⟶ D.obj i) :
    limitBaseChangeObj D c i ρ ⟶ (smallEtaleBaseChange π).obj Q :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst ρ.left (c.π.app i : c.pt ⟶ (D.obj i).left))
      (pullback.snd ρ.left (c.π.app i : c.pt ⟶ (D.obj i).left))
      ((congrArg (pullback.fst ρ.left (c.π.app i : c.pt ⟶ (D.obj i).left) ≫ ·)
        (MorphismProperty.Over.w ρ).symm).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (D.obj i).hom) pullback.condition).trans ((Category.assoc _ _ _).trans
            (congrArg (pullback.snd ρ.left (c.π.app i : c.pt ⟶ (D.obj i).left) ≫ ·)
              (hπ i)))))))
    (pullback.lift_snd _ _ _) trivial

/-- The morphism `Q ×_{Uᵢ} U ⟶ Q ×_X U` composed with the first projection `Q ×_X U ⟶ Q` is the
first projection `Q ×_{Uᵢ} U ⟶ Q`. -/
@[reassoc (attr := simp)]
theorem limitBaseChangeLift_left_fst (i : I) {Q : X.Etale} (ρ : Q ⟶ D.obj i) :
    (limitBaseChangeLift D c π hπ i ρ).left ≫ pullback.fst Q.hom π =
      pullback.fst ρ.left (c.π.app i : c.pt ⟶ (D.obj i).left) :=
  pullback.lift_fst _ _ _

/-- The morphism `Q₁ ×_{Uⱼ} U ⟶ Q₂ ×_{Uⱼ} U` induced by a morphism `Q₁ ⟶ Q₂` over `Uⱼ`. -/
def limitBaseChangeMap (j : I) {Q₁ Q₂ : X.Etale} {ρ₁ : Q₁ ⟶ D.obj j} {ρ₂ : Q₂ ⟶ D.obj j}
    (r : Q₁ ⟶ Q₂) (hr : r ≫ ρ₂ = ρ₁) :
    limitBaseChangeObj D c j ρ₁ ⟶ limitBaseChangeObj D c j ρ₂ :=
  have hr' : r.left ≫ ρ₂.left = ρ₁.left := congrArg (fun m => m.left) hr
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst ρ₁.left (c.π.app j : c.pt ⟶ (D.obj j).left) ≫ r.left)
      (pullback.snd ρ₁.left (c.π.app j : c.pt ⟶ (D.obj j).left))
      ((Category.assoc _ _ _).trans ((congrArg
        (pullback.fst ρ₁.left (c.π.app j : c.pt ⟶ (D.obj j).left) ≫ ·) hr').trans
          pullback.condition)))
    (pullback.lift_snd _ _ _) trivial

/-- The morphism `limitBaseChangeMap D c j r hr` composed with the first projection
`Q₂ ×_{Uⱼ} U ⟶ Q₂` is the first projection `Q₁ ×_{Uⱼ} U ⟶ Q₁` followed by `r`. -/
theorem limitBaseChangeMap_left_fst (j : I) {Q₁ Q₂ : X.Etale} {ρ₁ : Q₁ ⟶ D.obj j}
    {ρ₂ : Q₂ ⟶ D.obj j} (r : Q₁ ⟶ Q₂) (hr : r ≫ ρ₂ = ρ₁) :
    (limitBaseChangeMap D c j r hr).left ≫
        pullback.fst ρ₂.left (c.π.app j : c.pt ⟶ (D.obj j).left) =
      pullback.fst ρ₁.left (c.π.app j : c.pt ⟶ (D.obj j).left) ≫ r.left := by
  unfold limitBaseChangeMap
  exact pullback.lift_fst _ _ _

/-- **Naturality of the lift in the object over the stage.** -/
theorem limitBaseChangeLift_naturality (j : I) {Q₁ Q₂ : X.Etale} {ρ₁ : Q₁ ⟶ D.obj j}
    {ρ₂ : Q₂ ⟶ D.obj j} (r : Q₁ ⟶ Q₂) (hr : r ≫ ρ₂ = ρ₁) :
    limitBaseChangeLift D c π hπ j ρ₁ ≫ (smallEtaleBaseChange π).map r =
      limitBaseChangeMap D c j r hr ≫ limitBaseChangeLift D c π hπ j ρ₂ := by
  exact comp_map_eq_comp_of_left_fst π r _ _ _ (limitBaseChangeLift_left_fst D c π hπ j ρ₁)
    (limitBaseChangeLift_left_fst D c π hπ j ρ₂) (limitBaseChangeMap_left_fst D c j r hr)

/-- The morphism `Q₁ ×_{Uⱼ₁} U ⟶ Q₂ ×_{Uⱼ₂} U` induced by a morphism `r : Q₁ ⟶ Q₂` lying over a
transition `Uⱼ₁ ⟶ Uⱼ₂`. -/
def limitBaseChangeStageMap {j₁ j₂ : I} (h : j₁ ⟶ j₂) {Q₁ Q₂ : X.Etale} {ρ₁ : Q₁ ⟶ D.obj j₁}
    {ρ₂ : Q₂ ⟶ D.obj j₂} (r : Q₁ ⟶ Q₂) (hr : r ≫ ρ₂ = ρ₁ ≫ D.map h) :
    limitBaseChangeObj D c j₁ ρ₁ ⟶ limitBaseChangeObj D c j₂ ρ₂ :=
  have hr' : r.left ≫ ρ₂.left = ρ₁.left ≫ (D.map h).left := congrArg (fun m => m.left) hr
  have hcond : (pullback.fst ρ₁.left (c.π.app j₁ : c.pt ⟶ (D.obj j₁).left) ≫ r.left) ≫
      ρ₂.left = pullback.snd ρ₁.left (c.π.app j₁ : c.pt ⟶ (D.obj j₁).left) ≫
        (c.π.app j₂ : c.pt ⟶ (D.obj j₂).left) := by
    exact stage_cond _ _ r.left ρ₁.left ρ₂.left (D.map h).left _ _ hr' pullback.condition (c.w h)
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst ρ₁.left (c.π.app j₁ : c.pt ⟶ (D.obj j₁).left) ≫ r.left)
      (pullback.snd ρ₁.left (c.π.app j₁ : c.pt ⟶ (D.obj j₁).left)) hcond)
    (pullback.lift_snd _ _ _) trivial

/-- The morphism `limitBaseChangeStageMap D c h r hr` composed with the first projection
`Q₂ ×_{Uⱼ₂} U ⟶ Q₂` is the first projection `Q₁ ×_{Uⱼ₁} U ⟶ Q₁` followed by `r`. -/
theorem limitBaseChangeStageMap_left_fst {j₁ j₂ : I} (h : j₁ ⟶ j₂) {Q₁ Q₂ : X.Etale}
    {ρ₁ : Q₁ ⟶ D.obj j₁} {ρ₂ : Q₂ ⟶ D.obj j₂} (r : Q₁ ⟶ Q₂) (hr : r ≫ ρ₂ = ρ₁ ≫ D.map h) :
    (limitBaseChangeStageMap D c h r hr).left ≫
        pullback.fst ρ₂.left (c.π.app j₂ : c.pt ⟶ (D.obj j₂).left) =
      pullback.fst ρ₁.left (c.π.app j₁ : c.pt ⟶ (D.obj j₁).left) ≫ r.left := by
  unfold limitBaseChangeStageMap
  exact pullback.lift_fst _ _ _

/-- **Naturality of the lift across a transition.** -/
theorem limitBaseChangeLift_stage_naturality {j₁ j₂ : I} (h : j₁ ⟶ j₂) {Q₁ Q₂ : X.Etale}
    {ρ₁ : Q₁ ⟶ D.obj j₁} {ρ₂ : Q₂ ⟶ D.obj j₂} (r : Q₁ ⟶ Q₂) (hr : r ≫ ρ₂ = ρ₁ ≫ D.map h) :
    limitBaseChangeLift D c π hπ j₁ ρ₁ ≫ (smallEtaleBaseChange π).map r =
      limitBaseChangeStageMap D c h r hr ≫ limitBaseChangeLift D c π hπ j₂ ρ₂ := by
  exact comp_map_eq_comp_of_left_fst π r _ _ _ (limitBaseChangeLift_left_fst D c π hπ j₁ ρ₁)
    (limitBaseChangeLift_left_fst D c π hπ j₂ ρ₂) (limitBaseChangeStageMap_left_fst D c h r hr)

/-- `t` is represented over the chart `Q ×_{Uⱼ} U` by the section `b` of `F` over `Q`: the
pullback of `b`, restricted along the lift, is the restriction of `t`. -/
def IsLimitChartRep (t : ((smallEtaleInverseImage.{u, v} π).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 c.pt)))) (j : I) {Q : X.Etale} (ρ : Q ⟶ D.obj j)
    (b : F.obj.obj (op Q)) : Prop :=
  ((smallEtaleInverseImage.{u, v} π).obj F).obj.map (limitBaseChangeLift D c π hπ j ρ).op
      (smallEtaleSectionPullback.{u, v} π F Q b) =
    ((smallEtaleInverseImage.{u, v} π).obj F).obj.map
      ((isTerminalEtaleMkId c.pt).from (limitBaseChangeObj D c j ρ)).op t

/-- **Representatives restrict.** A representative over `Q₂` restricts, along any morphism over a
transition, to a representative over `Q₁`. -/
theorem IsLimitChartRep.map {t : ((smallEtaleInverseImage.{u, v} π).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 c.pt)))} {j₁ j₂ : I} (h : j₁ ⟶ j₂) {Q₁ Q₂ : X.Etale}
    {ρ₁ : Q₁ ⟶ D.obj j₁} {ρ₂ : Q₂ ⟶ D.obj j₂} (r : Q₁ ⟶ Q₂) (hr : r ≫ ρ₂ = ρ₁ ≫ D.map h)
    {b : F.obj.obj (op Q₂)} (hb : IsLimitChartRep D c π hπ F t j₂ ρ₂ b) :
    IsLimitChartRep D c π hπ F t j₁ ρ₁ (F.obj.map r.op b) := by
  unfold IsLimitChartRep at hb ⊢
  rw [← smallEtaleSectionPullback_map, ← FunctorToTypes.map_comp_apply, ← op_comp,
    limitBaseChangeLift_stage_naturality D c π hπ h r hr, op_comp, FunctorToTypes.map_comp_apply,
    hb, ← FunctorToTypes.map_comp_apply, ← op_comp]
  exact congrArg (fun m => ((smallEtaleInverseImage.{u, v} π).obj F).obj.map (Quiver.Hom.op m) t)
    ((isTerminalEtaleMkId c.pt).hom_ext _ _)

/-- **The stage lift and the base-change lift agree.** Restricting the stage lift of `Uⱼ` along
the final morphism of `Q ×_{Uⱼ} U` is the base-change lift of `Q` followed by the base change of
`ρ : Q ⟶ Uⱼ`. -/
theorem terminal_from_comp_limitStageLift (j : I) {Q : X.Etale} (ρ : Q ⟶ D.obj j) :
    (isTerminalEtaleMkId c.pt).from (limitBaseChangeObj D c j ρ) ≫ limitStageLift D c π hπ j =
      limitBaseChangeLift D c π hπ j ρ ≫ (smallEtaleBaseChange π).map ρ := by
  refine (comp_map_eq_comp_of_left_fst π ρ _ _ _ (limitBaseChangeLift_left_fst D c π hπ j ρ)
    (limitStageLift_left_fst D c π hπ j) ?_).symm
  rw [(Category.comp_id _).symm.trans
    (MorphismProperty.Over.w ((isTerminalEtaleMkId c.pt).from (limitBaseChangeObj D c j ρ)))]
  exact pullback.condition.symm

/-- Bookkeeping for `exists_stage_chart`, stated for plain schemes. -/
private lemma chart_chain₁ {P A B C S T Y Z : Scheme.{u}} (ei : P ⟶ A) (kl : A ⟶ B) (f1 : B ⟶ C)
    (s1 : B ⟶ S) (wh : C ⟶ Y) (pi : S ⟶ Y) (vh : A ⟶ S) (f2 : P ⟶ S) (cp : S ⟶ T) (dh : T ⟶ Y)
    (s2 : P ⟶ Z) (uu : Z ⟶ T) (h1 : f1 ≫ wh = s1 ≫ pi) (h2 : kl ≫ s1 = vh) (h3 : ei ≫ vh = f2)
    (h4 : cp ≫ dh = pi) (h5 : f2 ≫ cp = s2 ≫ uu) :
    (ei ≫ kl ≫ f1) ≫ wh = s2 ≫ uu ≫ dh := by
  rw [Category.assoc, Category.assoc, h1, ← Category.assoc kl, h2, ← Category.assoc, h3, ← h4,
    ← Category.assoc, h5, Category.assoc]

/-- Bookkeeping for `exists_stage_chart`, stated for plain schemes. -/
private lemma chart_chain₂ {P Z T T' Y W : Scheme.{u}} (ψ : P ⟶ W) (wh : W ⟶ Y) (fst : P ⟶ T')
    (snd : P ⟶ Z) (uu : Z ⟶ T) (dg : T' ⟶ T) (dh : T ⟶ Y) (dh' : T' ⟶ Y)
    (h1 : ψ ≫ wh = snd ≫ uu ≫ dh) (h2 : fst ≫ dg = snd ≫ uu) (h3 : dg ≫ dh = dh') :
    ψ ≫ wh = fst ≫ dh' := by
  rw [h1, ← h3, ← Category.assoc, ← h2, Category.assoc]

/-- Bookkeeping for `exists_stage_chart`, stated for plain schemes. -/
private lemma chart_chain₃ {V S T T' U : Scheme.{u}} (vh : V ⟶ S) (cj : S ⟶ T') (dg : T' ⟶ T)
    (ci : S ⟶ T) (θ₀ : V ⟶ U) (uu : U ⟶ T) (h1 : cj ≫ dg = ci) (h2 : θ₀ ≫ uu = vh ≫ ci) :
    (vh ≫ cj) ≫ dg = θ₀ ≫ uu := by
  rw [Category.assoc, h1, h2]

/-- Bookkeeping for `exists_stage_chart`, stated for plain schemes. -/
private lemma chart_chain₄ {V V' P Q W : Scheme.{u}} (θl : V ⟶ V') (fstρ : V' ⟶ Q) (θ₁ : V ⟶ Q)
    (ψ : Q ⟶ W) (eh : V ⟶ P) (ei : P ⟶ V) (cmp : P ⟶ Q) (φ : V ⟶ W) (h1 : θl ≫ fstρ = θ₁)
    (h2 : eh ≫ cmp = θ₁) (h3 : cmp ≫ ψ = ei ≫ φ) (h4 : eh ≫ ei = 𝟙 V) :
    θl ≫ fstρ ≫ ψ = φ := by
  rw [← Category.assoc, h1, ← h2, Category.assoc, h3, ← Category.assoc, h4, Category.id_comp]

/-- **A chart of the limit, with a morphism to a base change, comes from a stage.** Let `V` be a
quasi-compact and quasi-separated object of the small étale site of the limit `U` and
`k : V ⟶ W ×_X U` a morphism to the base change of an object of the small étale site of `X`.
Then there are a stage `Uⱼ`, a quasi-compact and quasi-separated object `ρ : Q ⟶ Uⱼ` over it, a
morphism `ψ : Q ⟶ W`, and an isomorphism `θ : V ≅ Q ×_{Uⱼ} U` (on underlying schemes) through
which `k` is the base change of `ψ`. This combines [Stacks, Tag 01ZM] part (1),
[Stacks, Tag 07RP] and [Stacks, Tag 01ZC]. -/
theorem exists_stage_chart [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e).left] [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] {V : c.pt.Etale} [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] {W : X.Etale} (k : V ⟶ (smallEtaleBaseChange π).obj W) :
    ∃ (j : I) (Q : X.Etale) (ρ : Q ⟶ D.obj j) (ψ : Q ⟶ W)
      (θ : V ⟶ limitBaseChangeObj D c j ρ), IsIso θ.left ∧ CompactSpace Q.left ∧
        QuasiSeparatedSpace Q.left ∧
        θ ≫ limitBaseChangeLift D c π hπ j ρ ≫ (smallEtaleBaseChange π).map ψ = k := by
  let D' := D ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  have : ∀ {i j : I} (e : i ⟶ j), IsAffineHom (D'.map e) :=
    fun e => inferInstanceAs (IsAffineHom (D.map e).left)
  have : ∀ i, CompactSpace (D'.obj i) := fun i => inferInstanceAs (CompactSpace (D.obj i).left)
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have : Etale (V.hom : V.left ⟶ c.pt) := V.prop
  obtain ⟨i₀, U', u', θ₀, hu', hcU, hqU, hpb⟩ :=
    @exists_isPullback_etale_of_etale I _ _ D' _ _ _ c hc V.left (V.hom : V.left ⟶ c.pt) _
      ‹CompactSpace V.left› ‹QuasiSeparatedSpace V.left›
  have := hu'
  have := hcU
  have := hqU
  have : QuasiCompact u' := quasiCompact_of_compactSpace u'
  have : QuasiSeparated u' := QuasiSeparated.of_quasiSeparatedSpace u'
  let e := hpb.flip.isoPullback
  let φ : V.left ⟶ W.left := k.left ≫ pullback.fst W.hom π
  have hkw : k.left ≫ pullback.snd W.hom π = V.hom := MorphismProperty.Over.w k
  have hφ : (e.inv ≫ φ) ≫ (W.hom : W.left ⟶ X) =
      pullback.snd (c.π.app i₀) u' ≫ u' ≫ (D.obj i₀).hom :=
    chart_chain₁ e.inv k.left (pullback.fst W.hom π) (pullback.snd W.hom π) W.hom π V.hom
      (pullback.fst (c.π.app i₀) u') (c.π.app i₀) (D.obj i₀).hom
      (pullback.snd (c.π.app i₀) u') u' pullback.condition hkw hpb.flip.isoPullback_inv_fst
      (hπ i₀) pullback.condition
  have : LocallyOfFinitePresentation (W.hom : W.left ⟶ X) := by
    have : Etale (W.hom : W.left ⟶ X) := W.prop
    infer_instance
  obtain ⟨j, g, ψ, hψw, hψc⟩ := exists_stage_hom_of_hom D' c hc i₀ u' (D.obj i₀).hom W.hom
    (e.inv ≫ φ) hφ
  have hfst : Etale (pullback.fst (D.map g).left u') := @Etale.instFstScheme _ _ _ _ _ hu'
  have : Etale ((D.obj j).hom : (D.obj j).left ⟶ X) := (D.obj j).prop
  let Q : X.Etale := Scheme.Etale.mk (pullback.fst (D.map g).left u' ≫ (D.obj j).hom)
  let ρ : Q ⟶ D.obj j := MorphismProperty.Over.homMk (pullback.fst (D.map g).left u') rfl trivial
  have hψQ : ψ ≫ (W.hom : W.left ⟶ X) = Q.hom :=
    chart_chain₂ ψ W.hom (pullback.fst (D.map g).left u') (pullback.snd (D.map g).left u') u'
      (D.map g).left (D.obj i₀).hom (D.obj j).hom hψw pullback.condition
      (MorphismProperty.Over.w (D.map g))
  let ψQ : Q ⟶ W := MorphismProperty.Over.homMk ψ hψQ trivial
  let θ₁ : V.left ⟶ Q.left :=
    pullback.lift ((V.hom : V.left ⟶ c.pt) ≫ c.π.app j) θ₀
      (chart_chain₃ V.hom (c.π.app j) (D.map g).left (c.π.app i₀) θ₀ u' (c.w g) hpb.w)
  let θ : V ⟶ limitBaseChangeObj D c j ρ :=
    MorphismProperty.Over.homMk (pullback.lift θ₁ V.hom (pullback.lift_fst _ _ _))
      (pullback.lift_snd _ _ _) trivial
  have hsq : IsPullback θ₁ (V.hom : V.left ⟶ c.pt) ρ.left (c.π.app j) := by
    have e1 : θ₁ ≫ pullback.snd (D.map g).left u' = θ₀ := pullback.lift_snd _ _ _
    have e2 : c.π.app j ≫ (D.map g).left = c.π.app i₀ := c.w g
    refine IsPullback.of_right (e1.symm ▸ e2.symm ▸ hpb) (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (D.map g).left u').flip
  have hθfst : θ.left ≫ pullback.fst ρ.left (c.π.app j : c.pt ⟶ (D.obj j).left) = θ₁ :=
    pullback.lift_fst _ _ _
  refine ⟨j, Q, ρ, ψQ, θ, ?_, ?_, ?_, ?_⟩
  · have : θ.left = hsq.isoPullback.hom := by
      apply pullback.hom_ext
      · exact hθfst.trans (IsPullback.isoPullback_hom_fst hsq).symm
      · exact (pullback.lift_snd _ _ _).trans (IsPullback.isoPullback_hom_snd hsq).symm
    exact this ▸ (inferInstance : IsIso hsq.isoPullback.hom)
  · have : QuasiCompact (pullback.fst (D.map g).left u') :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D.map g).left u').flip
        (inferInstanceAs (QuasiCompact u'))
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst (D.map g).left u') this _
  · have : QuasiSeparated (pullback.fst (D.map g).left u') :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D.map g).left u').flip
        (inferInstanceAs (QuasiSeparated u'))
    exact (quasiSeparated_iff_quasiSeparatedSpace (pullback.fst (D.map g).left u')).mp this
  · refine smallEtaleBaseChange_hom_ext π ?_
    have hc' : stageBaseChangeComparison D' c g u' ≫ ψ = e.inv ≫ φ := hψc
    have hθ₁ : e.hom ≫ stageBaseChangeComparison D' c g u' = θ₁ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hpb.flip.isoPullback_hom_fst]
        exact (pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, pullback.lift_snd, hpb.flip.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).symm
    have hl : (limitBaseChangeLift D c π hπ j ρ).left ≫
        ((smallEtaleBaseChange π).map ψQ).left ≫ pullback.fst W.hom π =
          pullback.fst ρ.left (c.π.app j : c.pt ⟶ (D.obj j).left) ≫ ψ :=
      (congrArg ((limitBaseChangeLift D c π hπ j ρ).left ≫ ·)
        (smallEtaleBaseChange_map_left_fst π ψQ)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ ψ) (limitBaseChangeLift_left_fst D c π hπ j ρ)))
    exact (congrArg (θ.left ≫ ·) hl).trans (chart_chain₄ θ.left _ θ₁ ψ e.hom e.inv
      (stageBaseChangeComparison D' c g u') φ hθfst hθ₁ hc' e.hom_inv_id)

/-- Points of a fibre product in the small étale site: a point of the second factor whose image
agrees with that of a point of the first is hit. -/
theorem exists_etalePullback_snd_eq {A B C : X.Etale} (f : A ⟶ C) (g : B ⟶ C) (a : A.left)
    (b : B.left) (e : f.left.base a = g.left.base b) :
    ∃ p : (pullback f g).left, (pullback.snd f g).left.base p = b :=
  exists_preimage_snd_of_isPullback
    ((IsPullback.of_hasPullback f g).map (Scheme.Etale.forget X ⋙ Over.forget X)) a b e

/-- A fibre product in the small étale site with a quasi-compact first factor over a
quasi-compact second factor is quasi-compact. -/
theorem compactSpace_etalePullback_left {A B C : X.Etale} (f : A ⟶ C) (g : B ⟶ C)
    [CompactSpace B.left] (hf : QuasiCompact f.left) : CompactSpace (pullback f g).left := by
  have : QuasiCompact (pullback.snd f g).left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback f g).map (Scheme.Etale.forget X ⋙ Over.forget X)) hf
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g).left

/-- **A section of the inverse image is represented by limit charts near each point.** -/
theorem exists_isLimitChartRep [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e).left] [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (t : ((smallEtaleInverseImage.{u, v} π).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))))
    (z : c.pt) :
    ∃ (j : I) (Q : X.Etale) (ρ : Q ⟶ D.obj j) (b : F.obj.obj (op Q)), CompactSpace Q.left ∧
      IsLimitChartRep D c π hπ F t j ρ b ∧
        z ∈ Set.range (limitBaseChangeObj D c j ρ).hom.base := by
  obtain ⟨V, a, W, k, s₀, hV, hz, hrel⟩ := exists_affine_local_rep π F t z
  obtain ⟨j, Q, ρ, ψ, θ, hθ, hQc, hQq, hk⟩ := exists_stage_chart D c π hπ hc k
  refine ⟨j, Q, ρ, F.obj.map ψ.op s₀, hQc, ?_, ?_⟩
  · have : IsIso ((Scheme.Etale.forget c.pt ⋙ Over.forget c.pt).map θ) := hθ
    have : IsIso θ := isIso_of_reflects_iso θ (Scheme.Etale.forget c.pt ⋙ Over.forget c.pt)
    unfold IsLimitChartRep
    rw [← smallEtaleSectionPullback_map, ← FunctorToTypes.map_comp_apply, ← op_comp]
    have hk' : limitBaseChangeLift D c π hπ j ρ ≫ (smallEtaleBaseChange π).map ψ = inv θ ≫ k := by
      rw [← hk, IsIso.inv_hom_id_assoc]
    rw [hk', op_comp, FunctorToTypes.map_comp_apply, ← hrel, ← FunctorToTypes.map_comp_apply,
      ← op_comp]
    exact congrArg (fun m => ((smallEtaleInverseImage.{u, v} π).obj F).obj.map (Quiver.Hom.op m) t)
      ((isTerminalEtaleMkId c.pt).hom_ext _ _)
  · obtain ⟨v, rfl⟩ := hz
    refine ⟨θ.left.base v, ?_⟩
    have h1 : θ.left ≫ (limitBaseChangeObj D c j ρ).hom = V.hom := MorphismProperty.Over.w θ
    have h2 : a.left ≫ (Scheme.Etale.mk (𝟙 c.pt)).hom = V.hom := MorphismProperty.Over.w a
    have h3 := congrArg (fun m => m.base v) (h1.trans h2.symm)
    simp only [Scheme.Hom.comp_apply] at h3
    exact h3

/-- **Limit-chart representatives pass to later stages.** -/
theorem IsLimitChartRep.stage {t : ((smallEtaleInverseImage.{u, v} π).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 c.pt)))} {j j' : I} (h : j' ⟶ j) {Q : X.Etale}
    {ρ : Q ⟶ D.obj j} {b : F.obj.obj (op Q)} (hb : IsLimitChartRep D c π hπ F t j ρ b) :
    IsLimitChartRep D c π hπ F t j' (pullback.snd ρ (D.map h))
      (F.obj.map (pullback.fst ρ (D.map h)).op b) :=
  hb.map D c π hπ F h _ pullback.condition

/-- A point of the limit over the chart `Q ×_{Uⱼ} U` lies over the restricted chart at any later
stage. -/
theorem mem_range_limitBaseChangeObj_stage {j j' : I} (h : j' ⟶ j) {Q : X.Etale}
    (ρ : Q ⟶ D.obj j) {z : c.pt} (hz : z ∈ Set.range (limitBaseChangeObj D c j ρ).hom.base) :
    z ∈ Set.range (limitBaseChangeObj D c j' (pullback.snd ρ (D.map h))).hom.base := by
  obtain ⟨p, rfl⟩ := hz
  let p₁ := (pullback.fst ρ.left (c.π.app j : c.pt ⟶ (D.obj j).left)).base p
  let z := (pullback.snd ρ.left (c.π.app j : c.pt ⟶ (D.obj j).left)).base p
  have e1 : ρ.left.base p₁ =
      (D.map h).left.base ((c.π.app j' : c.pt ⟶ (D.obj j').left).base z) := by
    have h1 := congrArg (fun m => m.base p)
      (pullback.condition (f := ρ.left) (g := (c.π.app j : c.pt ⟶ (D.obj j).left)))
    have h2 := congrArg (fun m => m.base z) (c.w h)
    simp only [Scheme.Hom.comp_apply] at h1 h2
    exact h1.trans h2.symm
  obtain ⟨q, hq⟩ := exists_etalePullback_snd_eq ρ (D.map h) p₁ _ e1
  obtain ⟨r, hr⟩ := exists_preimage_snd_of_isPullback (IsPullback.of_hasPullback
    (pullback.snd ρ (D.map h)).left (c.π.app j' : c.pt ⟶ (D.obj j').left)) q z hq
  exact ⟨r, hr⟩

/-- **Two sections over a scheme étale over a stage, with the same pullback to the limit, agree
over a later stage.** Let `Q ⟶ Uᵢ` be a morphism of the small étale site of `X` with `Q`
quasi-compact. If two sections of `F` over `Q` have the same pullback to `Q ×_{Uᵢ} U`, they agree
over `Q ×_{Uᵢ} Uⱼ` for some `j ⟶ i`. Equality of the pullbacks is witnessed locally in the left
Kan extension computing the inverse image, hence over objects `W ⟶ Q` whose images cover the
image of `Q ×_{Uᵢ} U` in `Q`; the complement of that union is a closed subset of the
quasi-compact `Q` missing the image of the limit, so it misses the image of `Q ×_{Uᵢ} Uⱼ` for
some `j` (Stacks 05F3), and the two sections agree on the covering of `Q ×_{Uᵢ} Uⱼ` by the base
changes of the `W`. -/
theorem exists_eq_of_limitBaseChange_eq [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e).left] (i : I) {Q : X.Etale}
    (ρ : Q ⟶ D.obj i) [CompactSpace Q.left] (s s' : F.obj.obj (op Q))
    (h : ((smallEtaleInverseImage.{u, v} π).obj F).obj.map (limitBaseChangeLift D c π hπ i ρ).op
        (smallEtaleSectionPullback.{u, v} π F Q s) =
      ((smallEtaleInverseImage.{u, v} π).obj F).obj.map (limitBaseChangeLift D c π hπ i ρ).op
        (smallEtaleSectionPullback.{u, v} π F Q s')) :
    ∃ (j : I) (g : j ⟶ i), F.obj.map (pullback.fst ρ (D.map g)).op s =
      F.obj.map (pullback.fst ρ (D.map g)).op s' := by
  have hlimE : ∀ z, (pullback.fst ρ.left (c.π.app i : c.pt ⟶ (D.obj i).left)).base z ∈
      agreementLocus F s s' := fun z => by
    have := fst_mem_agreementLocus π F (limitBaseChangeLift D c π hπ i ρ) s s' h z
    rwa [limitBaseChangeLift_left_fst] at this
  obtain ⟨j, g, hg⟩ := exists_stage_forall_mem_of_isOpen D c hc i ρ.left
    (isOpen_agreementLocus F s s') fun v q hq => by
      obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback q v hq
      rw [← hy]
      exact hlimE y
  refine ⟨j, g, map_eq_of_range_subset_agreementLocus F (pullback.fst ρ (D.map g)) s s' ?_⟩
  rintro _ ⟨x, rfl⟩
  refine hg ((pullback.snd ρ (D.map g)).left.base x) _ ?_
  have := congrArg (fun m => m.base x) ((IsPullback.of_hasPullback ρ (D.map g)).map
    (Scheme.Etale.forget X ⋙ Over.forget X)).w
  simp only [Functor.comp_map] at this
  exact this

/-- A fibre product in the small étale site of quasi-compact objects over a quasi-separated one is
quasi-compact. -/
theorem compactSpace_etalePullback {A B C : X.Etale} (f : A ⟶ C) (g : B ⟶ C)
    [CompactSpace A.left] [CompactSpace B.left] [QuasiSeparatedSpace C.left] :
    CompactSpace (pullback f g).left :=
  compactSpace_etalePullback_left f g (quasiCompact_of_compactSpace f.left)

/-- **Stacks 03Q9 for global sections of sheaves of sets, existence half.** Every global section
of `π⁻¹F` over the limit `U` of a cofiltered system of quasi-compact and quasi-separated schemes
`Uᵢ` étale over `X`, with affine transition morphisms, is the pullback of a section of `F` over
some stage. The section is represented by sections of `F` over finitely many charts, which are
descended to a common stage where they cover it (Stacks 05F3) and agree on overlaps (by
`exists_eq_of_limitBaseChange_eq`), hence glue. -/
theorem exists_limitStagePullback_eq [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e).left] [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (t : ((smallEtaleInverseImage.{u, v} π).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))) :
    ∃ (i : I) (s : F.obj.obj (op (D.obj i))), limitStagePullback D c π hπ F i s = t := by
  classical
  let D' := D ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  have : ∀ {i j : I} (e : i ⟶ j), IsAffineHom (D'.map e) :=
    fun e => inferInstanceAs (IsAffineHom (D.map e).left)
  have : ∀ i, CompactSpace (D'.obj i) := fun i => inferInstanceAs (CompactSpace (D.obj i).left)
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have : CompactSpace c.pt := (compactSpace_and_quasiSeparatedSpace_pt D' c hc).1
  choose j Q ρ b hQ hrep hz using exists_isLimitChartRep D c π hπ F hc t
  have hopen : ∀ z, IsOpen (Set.range (limitBaseChangeObj D c (j z) (ρ z)).hom.base) := by
    intro z
    have : Etale ((limitBaseChangeObj D c (j z) (ρ z)).hom :
      (limitBaseChangeObj D c (j z) (ρ z)).left ⟶ c.pt) := (limitBaseChangeObj D c (j z) (ρ z)).prop
    exact ((limitBaseChangeObj D c (j z) (ρ z)).hom :
      (limitBaseChangeObj D c (j z) (ρ z)).left ⟶ c.pt).isOpenMap.isOpen_range
  obtain ⟨Z₀, hZ₀⟩ := isCompact_univ.elim_finite_subcover _ hopen
    (fun z _ => Set.mem_iUnion.mpr ⟨z, hz z⟩)
  let M := ↥Z₀
  -- a first common stage
  obtain ⟨b₀, hb₀⟩ := IsCofiltered.inf_objs_exists (Z₀.image j)
  have hg : ∀ m : M, Nonempty (b₀ ⟶ j m.1) := fun m => hb₀ (Finset.mem_image_of_mem j m.2)
  let g : ∀ m : M, b₀ ⟶ j m.1 := fun m => (hg m).some
  let ρ₀ : ∀ m : M, pullback (ρ m.1) (D.map (g m)) ⟶ D.obj b₀ :=
    fun m => pullback.snd (ρ m.1) (D.map (g m))
  have hrep₀ : ∀ m : M, IsLimitChartRep D c π hπ F t b₀ (ρ₀ m)
      (F.obj.map (pullback.fst (ρ m.1) (D.map (g m))).op (b m.1)) :=
    fun m => (hrep m.1).stage D c π hπ F (g m)
  have hQ₀ : ∀ m : M, CompactSpace (pullback (ρ m.1) (D.map (g m))).left := fun m => by
    have := hQ m.1
    exact compactSpace_etalePullback _ _
  have hcov₀ : ∀ z : c.pt, ∃ m : M,
      z ∈ Set.range (limitBaseChangeObj D c b₀ (ρ₀ m)).hom.base := by
    intro z
    have hz' : z ∈ ⋃ i ∈ Z₀, Set.range (limitBaseChangeObj D c (j i) (ρ i)).hom.base :=
      hZ₀ (Set.mem_univ z)
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨i, hi, hzi⟩ := hz'
    exact ⟨⟨i, hi⟩, mem_range_limitBaseChangeObj_stage D c (g ⟨i, hi⟩) (ρ i) hzi⟩
  -- a stage covered by the charts
  obtain ⟨b₁, e₁, hcov₁'⟩ := exists_stage_jointlySurjective D' c hc b₀
    (fun m : M => (pullback (ρ m.1) (D.map (g m))).left) (fun m => (ρ₀ m).left)
    (fun m => (ρ₀ m).left.isOpenMap) (fun z => by
      obtain ⟨m, y, hy⟩ := hcov₀ z
      exact ⟨m, y, hy⟩)
  let ρ₁ : ∀ m : M, pullback (ρ₀ m) (D.map e₁) ⟶ D.obj b₁ := fun m => pullback.snd (ρ₀ m) (D.map e₁)
  let x₁ : ∀ m : M, F.obj.obj (op (pullback (ρ₀ m) (D.map e₁))) := fun m =>
    F.obj.map (pullback.fst (ρ₀ m) (D.map e₁)).op
      (F.obj.map (pullback.fst (ρ m.1) (D.map (g m))).op (b m.1))
  have hrep₁ : ∀ m : M, IsLimitChartRep D c π hπ F t b₁ (ρ₁ m) (x₁ m) :=
    fun m => (hrep₀ m).stage D c π hπ F e₁
  have hQ₁ : ∀ m : M, CompactSpace (pullback (ρ₀ m) (D.map e₁)).left :=
    fun m => compactSpace_etalePullback _ _
  have hcov₁ : ∀ x : (D.obj b₁).left, ∃ m : M, ∃ y : (pullback (ρ₀ m) (D.map e₁)).left,
      (ρ₁ m).left.base y = x := by
    intro x
    obtain ⟨m, y, hy⟩ := hcov₁' x
    obtain ⟨p, hp⟩ := exists_etalePullback_snd_eq (ρ₀ m) (D.map e₁)
      ((pullback.fst (ρ₀ m).left (D.map e₁).left).base y) x (by
        have := congrArg (fun k => k.base y)
          (pullback.condition (f := (ρ₀ m).left) (g := (D.map e₁).left))
        simp only at this
        exact this.trans (congrArg _ hy))
    exact ⟨m, p, hp⟩
  -- the charts agree on overlaps at a later stage
  have hpair : ∀ mm : M × M, ∃ (k : I) (gk : k ⟶ b₁),
      F.obj.map (pullback.fst (pullback.fst (ρ₁ mm.1) (ρ₁ mm.2) ≫ ρ₁ mm.1) (D.map gk)).op
          (F.obj.map (pullback.fst (ρ₁ mm.1) (ρ₁ mm.2)).op (x₁ mm.1)) =
        F.obj.map (pullback.fst (pullback.fst (ρ₁ mm.1) (ρ₁ mm.2) ≫ ρ₁ mm.1) (D.map gk)).op
          (F.obj.map (pullback.snd (ρ₁ mm.1) (ρ₁ mm.2)).op (x₁ mm.2)) := by
    intro mm
    let P := pullback (ρ₁ mm.1) (ρ₁ mm.2)
    let ρP : P ⟶ D.obj b₁ := pullback.fst (ρ₁ mm.1) (ρ₁ mm.2) ≫ ρ₁ mm.1
    have h1 := (hrep₁ mm.1).map D c π hπ F (𝟙 b₁) (pullback.fst (ρ₁ mm.1) (ρ₁ mm.2))
      (ρ₁ := ρP) (by rw [D.map_id, Category.comp_id])
    have h2 := (hrep₁ mm.2).map D c π hπ F (𝟙 b₁) (pullback.snd (ρ₁ mm.1) (ρ₁ mm.2))
      (ρ₁ := ρP) (by rw [D.map_id, Category.comp_id, ← pullback.condition])
    have : CompactSpace P.left := compactSpace_etalePullback _ _
    exact exists_eq_of_limitBaseChange_eq D c π hπ F hc b₁ ρP _ _ (h1.trans h2.symm)
  choose k gk hk using hpair
  obtain ⟨b₂, gb, fb, hfb⟩ := exists_common_refinement b₁ k gk
  -- the final charts
  let ρ₂ : ∀ m : M, pullback (ρ₁ m) (D.map gb) ⟶ D.obj b₂ := fun m => pullback.snd (ρ₁ m) (D.map gb)
  let x₂ : ∀ m : M, F.obj.obj (op (pullback (ρ₁ m) (D.map gb))) := fun m =>
    F.obj.map (pullback.fst (ρ₁ m) (D.map gb)).op (x₁ m)
  have hcov₂ : Sieve.ofArrows _ ρ₂ ∈ Scheme.smallEtaleTopology X (D.obj b₂) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨m, y, hy⟩ := hcov₁ ((D.map gb).left.base x)
    obtain ⟨p, hp⟩ := exists_etalePullback_snd_eq (ρ₁ m) (D.map gb) y x hy
    exact Set.mem_iUnion.mpr ⟨m, p, hp⟩
  have hsheaf : Presieve.IsSheafFor F.obj (Presieve.ofArrows _ ρ₂) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      (((isSheaf_iff_isSheaf_of_type _ _).1 F.property) _ hcov₂)
  have hcompat : Presieve.Arrows.Compatible F.obj ρ₂ x₂ := by
    intro m m' Z gi gj hij
    let mm : M × M := (m, m')
    let ℓ₀ : Z ⟶ pullback (ρ₁ m) (ρ₁ m') :=
      pullback.lift (gi ≫ pullback.fst (ρ₁ m) (D.map gb)) (gj ≫ pullback.fst (ρ₁ m') (D.map gb))
        (by rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition,
          ← Category.assoc, hij, Category.assoc])
    let ℓ : Z ⟶ pullback (pullback.fst (ρ₁ m) (ρ₁ m') ≫ ρ₁ m) (D.map (gk mm)) :=
      pullback.lift ℓ₀ (gi ≫ ρ₂ m ≫ D.map (fb mm)) (by
        rw [pullback.lift_fst_assoc]
        simp only [Category.assoc]
        rw [← Functor.map_comp, hfb, pullback.condition])
    have e1 : gi ≫ pullback.fst (ρ₁ m) (D.map gb) =
        ℓ ≫ pullback.fst _ (D.map (gk mm)) ≫ pullback.fst (ρ₁ m) (ρ₁ m') := by
      rw [pullback.lift_fst_assoc, pullback.lift_fst]
    have e2 : gj ≫ pullback.fst (ρ₁ m') (D.map gb) =
        ℓ ≫ pullback.fst _ (D.map (gk mm)) ≫ pullback.snd (ρ₁ m) (ρ₁ m') := by
      rw [pullback.lift_fst_assoc, pullback.lift_snd]
    calc F.obj.map gi.op (x₂ m)
        = F.obj.map (gi ≫ pullback.fst (ρ₁ m) (D.map gb)).op (x₁ m) := by
          rw [op_comp, FunctorToTypes.map_comp_apply]
      _ = F.obj.map (ℓ ≫ pullback.fst _ (D.map (gk mm)) ≫ pullback.fst (ρ₁ m) (ρ₁ m')).op
            (x₁ m) := by rw [e1]
      _ = F.obj.map ℓ.op (F.obj.map (pullback.fst _ (D.map (gk mm))).op
            (F.obj.map (pullback.fst (ρ₁ m) (ρ₁ m')).op (x₁ m))) := by
          simp only [op_comp, FunctorToTypes.map_comp_apply]
      _ = F.obj.map ℓ.op (F.obj.map (pullback.fst _ (D.map (gk mm))).op
            (F.obj.map (pullback.snd (ρ₁ m) (ρ₁ m')).op (x₁ m'))) := by rw [hk mm]
      _ = F.obj.map (ℓ ≫ pullback.fst _ (D.map (gk mm)) ≫ pullback.snd (ρ₁ m) (ρ₁ m')).op
            (x₁ m') := by simp only [op_comp, FunctorToTypes.map_comp_apply]
      _ = F.obj.map gj.op (x₂ m') := by
          rw [← e2, op_comp, FunctorToTypes.map_comp_apply]
  obtain ⟨t₀, ht₀, -⟩ := (Presieve.isSheafFor_arrows_iff F.obj ρ₂).mp hsheaf x₂ hcompat
  refine ⟨b₂, t₀, ?_⟩
  -- the glued section pulls back to `t`
  have hrep₂ : ∀ m : M, IsLimitChartRep D c π hπ F t b₂ (ρ₂ m) (x₂ m) :=
    fun m => (hrep₁ m).stage D c π hπ F gb
  let Y : M → c.pt.Etale := fun m => limitBaseChangeObj D c b₂ (ρ₂ m)
  let fY : ∀ m, Y m ⟶ Scheme.Etale.mk (𝟙 c.pt) := fun m => (isTerminalEtaleMkId c.pt).from (Y m)
  have hYcov : Sieve.ofArrows Y fY ∈ Scheme.smallEtaleTopology c.pt (Scheme.Etale.mk (𝟙 c.pt)) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨m, hm⟩ := hcov₀ z
    have hm₂ := mem_range_limitBaseChangeObj_stage D c gb (ρ₁ m)
      (mem_range_limitBaseChangeObj_stage D c e₁ (ρ₀ m) hm)
    obtain ⟨y, hy⟩ := hm₂
    refine Set.mem_iUnion.mpr ⟨m, y, ?_⟩
    have := congrArg (fun k => k.base y) (MorphismProperty.Over.w (fY m))
    simp only [Scheme.Hom.comp_apply] at this
    exact this.trans hy
  refine ((((isSheaf_iff_isSheaf_of_type _ _).1
    ((smallEtaleInverseImage.{u, v} π).obj F).property) _ hYcov).isSeparatedFor).ext ?_
  rintro T f ⟨T', r, _, ⟨m⟩, rfl⟩
  rw [op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply]
  congr 1
  rw [limitStagePullback, ← FunctorToTypes.map_comp_apply, ← op_comp,
    terminal_from_comp_limitStageLift, op_comp, FunctorToTypes.map_comp_apply,
    smallEtaleSectionPullback_map, ht₀ m]
  exact hrep₂ m

end Limit

end Stacks.EtaleCohomology

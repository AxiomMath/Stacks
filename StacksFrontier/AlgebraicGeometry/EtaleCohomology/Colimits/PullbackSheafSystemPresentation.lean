module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackCompApp

/-!
# The inverse image of a sheaf on the base as the colimit of its inverse images to the stages

Let `X = lim X_i` be the limit of a directed inverse system of schemes, and let `ι_i : X_i ⟶ S`
be a compatible family of morphisms to a scheme `S`, with induced morphism `g : X ⟶ S`. For an
abelian sheaf `G` on the small étale site of `S`, the inverse images `ι_i⁻¹ G` form a system of
sheaves (`Stacks.EtaleCohomology.EtaleSheafSystem.ofCocone`), and `g⁻¹ G` is its colimit in the
sense of [Stacks, Tag 0EZL]: the comparisons `f_i⁻¹ ι_i⁻¹ G ≅ g⁻¹ G` of inverse images along
`g = ι_i ∘ f_i` are compatible with the transition maps, and since they are isomorphisms and the
index set is directed, they exhibit `g⁻¹ G` as the colimit of the system `f_i⁻¹ ι_i⁻¹ G`.

This is the situation in which [Stacks, Tag 09YQ] is applied in [Stacks, Tag 0DV7]: the system
`ι_i⁻¹ G` satisfies the hypotheses of that theorem with colimit sheaf `g⁻¹ G`.

Similarly, for a morphism `e : (Y_i) ⟶ (T_i)` of inverse systems of schemes and a morphism
`e : Y ⟶ T` of cones over it, the inverse image along `e` of a presentation `ℱ = colim p_i⁻¹ℱ_i`
on `T` is a presentation `e⁻¹ℱ = colim q_i⁻¹e_i⁻¹ℱ_i` of the system of inverse images
`Stacks.EtaleCohomology.EtaleSheafSystem.pullback`.

## Main definitions

* `Stacks.EtaleCohomology.EtaleSheafSystem.pullbackLeg`: the legs `q_i⁻¹e_i⁻¹ℱ_i ⟶ e⁻¹ℱ`.

## Main results

* `Stacks.EtaleCohomology.EtaleSheafSystem.isPullbackCocone_ofCocone`: the comparisons of inverse
  images are compatible with the transition maps of the system.
* `Stacks.EtaleCohomology.EtaleSheafSystem.isPullbackColimitPresentation_ofCocone`: they exhibit
  `g⁻¹ G` as the colimit of the system.
* `Stacks.EtaleCohomology.EtaleSheafSystem.isPullbackCocone_pullback`,
  `Stacks.EtaleCohomology.EtaleSheafSystem.isPullbackColimitPresentation_pullback`: the inverse
  image of a presentation is a presentation.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {S : Scheme.{u}}
  (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
  (c : Cone D) (g : c.pt ⟶ S) (hg : ∀ i, c.π.app i ≫ ι i = g)
  (G : Sheaf (smallEtaleTopology S) Ab.{u + 1})

/-- The comparison `f_i⁻¹ ι_i⁻¹ G ≅ g⁻¹ G` of inverse images along `g = f_i ≫ ι_i`, as the legs
presenting `g⁻¹ G` over the system of inverse images of `G`. -/
noncomputable abbrev EtaleSheafSystem.ofCoconeLeg (i : Iᵒᵖ) :
    (smallEtalePullbackAb (c.π.app i)).obj ((EtaleSheafSystem.ofCocone ι hι G).obj i) ⟶
      (smallEtalePullbackAb g).obj G :=
  (smallEtalePullbackAbComp' (c.π.app i) (ι i) g (hg i).symm).hom.app G

/-- **The comparisons of inverse images are compatible with the transition maps** of the system of
inverse images of one sheaf. This is the associativity of the comparisons of inverse images. -/
theorem EtaleSheafSystem.isPullbackCocone_ofCocone :
    LimitHigherDirectImage.IsPullbackCocone c (EtaleSheafSystem.ofCocone ι hι G)
      (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G) := by
  intro i j a
  have hp := smallEtalePullbackAbComp'_assoc_app (c.π.app i) (D.map a) (ι j) (c.π.app j)
    (c.w a).symm (ι i) (hι a).symm g (hg j).symm (hg i).symm G
  change (conePullbackComp c a).inv.app _ ≫ (smallEtalePullbackAb (c.π.app i)).map
    ((smallEtalePullbackAbComp' (D.map a) (ι j) (ι i) (hι a).symm).hom.app G) ≫
      (smallEtalePullbackAbComp' (c.π.app i) (ι i) g (hg i).symm).hom.app G =
    (smallEtalePullbackAbComp' (c.π.app j) (ι j) g (hg j).symm).hom.app G
  rw [conePullbackComp_eq, ← hp, Iso.inv_hom_id_app_assoc]

/-- **The inverse image of a sheaf on the base is the colimit of its inverse images to the
stages**: over a directed set, the comparisons `f_i⁻¹ ι_i⁻¹ G ≅ g⁻¹ G` present `g⁻¹ G` as the
colimit of the system `ι_i⁻¹ G` in the sense of [Stacks, Tag 0EZL]. -/
theorem EtaleSheafSystem.isPullbackColimitPresentation_ofCocone [IsDirected I (· ≤ ·)]
    [Nonempty I] :
    LimitHigherDirectImage.IsPullbackColimitPresentation c ((smallEtalePullbackAb g).obj G)
      (EtaleSheafSystem.ofCocone ι hι G) (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G) :=
  have : ∀ i, IsIso (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G i) := fun i =>
    ((smallEtalePullbackAbComp' (c.π.app i) (ι i) g (hg i).symm).app G).isIso_hom
  IsSystemColimit.of_isIso fun a => (Category.assoc _ _ _).trans
    (EtaleSheafSystem.isPullbackCocone_ofCocone ι hι c g hg G a)

/-! ### The inverse image of a colimit presentation along a morphism of systems -/

section MorphismOfSystems

local notation "App" => smallEtalePullbackAbCompApp

/-- The comparison of inverse images along the factorisation of a projection, on components. -/
theorem conePullbackComp_inv_app_eq {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D) {i j : Iᵒᵖ}
    (a : i ⟶ j) (M : Sheaf (smallEtaleTopology (D.obj j)) Ab.{u + 1}) :
    (conePullbackComp c a).inv.app M = (App (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm M).inv :=
  congrArg (fun z => z.inv.app M) (conePullbackComp_eq c a)

/-- The rearrangement behind
`Stacks.EtaleCohomology.EtaleSheafSystem.pullback_pullbackDiagramMap`, in an arbitrary category:
two naturality squares, three associativity squares and the cancellations. -/
private theorem pullbackDiagramMap_algebra {E : Type*} [Category* E]
    {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ o₁₁ : E}
    (Lx : o₁ ⟶ o₂) (Ly : o₂ ⟶ o₃) (Lh : o₂ ⟶ o₁)
    (hx : Lx ≫ Lh = 𝟙 o₁) (Eh : o₂ ⟶ o₄) (Eh₀ : o₃ ⟶ o₅) (v : o₄ ⟶ o₅) (nE : Ly ≫ Eh₀ = Eh ≫ v)
    (Qi : o₄ ⟶ o₆) (Qi₀ : o₅ ⟶ o₇) (t : o₆ ⟶ o₇) (nQ : v ≫ Qi₀ = Qi ≫ t) (Qh : o₆ ⟶ o₄)
    (hQ : Qi ≫ Qh = 𝟙 o₄) (Xv : o₄ ⟶ o₈) (n : o₆ ⟶ o₉) (Yv : o₉ ⟶ o₈) (A₁ : Qh ≫ Xv = n ≫ Yv)
    (Zh : o₁ ⟶ o₈) (A₂ : Eh ≫ Xv = Lh ≫ Zh) (Ri : o₈ ⟶ o₁₀) (Rh : o₁₀ ⟶ o₈)
    (hR : Ri ≫ Rh = 𝟙 o₈) (Si : o₁₀ ⟶ o₁₁) (Sh : o₁₁ ⟶ o₁₀) (hS : Si ≫ Sh = 𝟙 o₁₀)
    (k : o₁₁ ⟶ o₉) (A₃ : Sh ≫ Rh = k ≫ Yv) (n' : o₉ ⟶ o₆) (hn : n' ≫ n = 𝟙 o₉)
    (hn' : n ≫ n' = 𝟙 o₆) (Yv' : o₈ ⟶ o₉) (hY : Yv ≫ Yv' = 𝟙 o₉) (P : o₁₁ ⟶ o₇)
    (hP : P = k ≫ n' ≫ t) :
    Lx ≫ Ly ≫ Eh₀ ≫ Qi₀ = Zh ≫ Ri ≫ Si ≫ P := by
  have hiso : Lx ≫ Eh ≫ Qi = Zh ≫ Ri ≫ Si ≫ k ≫ n' := by
    have e₁ : (Lx ≫ Eh ≫ Qi) ≫ n ≫ Yv = Zh := by
      simp only [Category.assoc]
      rw [← A₁, reassoc_of% hQ, A₂, reassoc_of% hx]
    have e₂ : (Zh ≫ Ri ≫ Si ≫ k ≫ n') ≫ n ≫ Yv = Zh := by
      simp only [Category.assoc]
      rw [reassoc_of% hn, ← A₃, reassoc_of% hS, hR, Category.comp_id]
    have hK : (n ≫ Yv) ≫ Yv' ≫ n' = 𝟙 o₆ := by
      simp only [Category.assoc]
      rw [reassoc_of% hY, hn']
    calc Lx ≫ Eh ≫ Qi = ((Lx ≫ Eh ≫ Qi) ≫ n ≫ Yv) ≫ Yv' ≫ n' := by
          rw [Category.assoc _ (n ≫ Yv), hK, Category.comp_id]
      _ = ((Zh ≫ Ri ≫ Si ≫ k ≫ n') ≫ n ≫ Yv) ≫ Yv' ≫ n' := by rw [e₁, e₂]
      _ = Zh ≫ Ri ≫ Si ≫ k ≫ n' := by
          rw [Category.assoc _ (n ≫ Yv), hK, Category.comp_id]
  rw [hP, reassoc_of% nE, nQ, reassoc_of% hiso]

/-- The rearrangement behind `Stacks.EtaleCohomology.EtaleSheafSystem.isPullbackCocone_pullback`,
in an arbitrary category. -/
private theorem cocone_algebra {E : Type*} [Category* E] {A B C D D' Z : E} (LT : A ⟶ B)
    (θi : B ⟶ C) (θj : A ⟶ D) (c : D ⟶ D') (m : D' ⟶ C) (h : LT ≫ θi = θj ≫ c ≫ m)
    (ιi : C ⟶ Z) (ιj : D ⟶ Z) (Lιi : B ⟶ Z) (Lιj : A ⟶ Z) (hi : θi ≫ ιi = Lιi)
    (hj : θj ≫ ιj = Lιj) (hT : LT ≫ Lιi = Lιj) (θj' : D ⟶ A) (hθ : θj' ≫ θj = 𝟙 D) :
    c ≫ m ≫ ιi = ιj := by
  calc c ≫ m ≫ ιi = θj' ≫ (θj ≫ c ≫ m) ≫ ιi := by
        simp only [Category.assoc, reassoc_of% hθ]
    _ = ιj := by
        rw [← h]
        simp only [Category.assoc]
        rw [hi, hT, ← hj, reassoc_of% hθ]

variable {DY DT : Iᵒᵖ ⥤ Scheme.{u}} (e : DY ⟶ DT) {cY : Cone DY} {cT : Cone DT}
  (eL : cY.pt ⟶ cT.pt) (heL : ∀ i, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
  (F : EtaleSheafSystem DT Ab.{u + 1})

/-- The legs `q_i⁻¹e_i⁻¹ℱ_i ⟶ e⁻¹ℱ` of the inverse image along `e : Y ⟶ T` of a presentation
`ι_i : p_i⁻¹ℱ_i ⟶ ℱ`: the comparison `q_i⁻¹e_i⁻¹ ≅ e⁻¹p_i⁻¹` through the diagonal of the projection
square `e ≫ p_i = q_i ≫ e_i`, followed by `e⁻¹ι_i`. -/
noncomputable def EtaleSheafSystem.pullbackLeg {𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cY.π.app i)).obj ((smallEtalePullbackAb (e.app i)).obj (F.obj i)) ⟶
      (smallEtalePullbackAb eL).obj 𝓕 :=
  (App (cY.π.app i) (e.app i) (cY.π.app i ≫ e.app i) rfl (F.obj i)).hom ≫
    (App eL (cT.π.app i) (cY.π.app i ≫ e.app i) (heL i).symm (F.obj i)).inv ≫
    (smallEtalePullbackAb eL).map (ι i)

/-- The comparison `e⁻¹p_i⁻¹ℱ_i ≅ q_i⁻¹e_i⁻¹ℱ_i` of the projection square, as a morphism. -/
noncomputable def EtaleSheafSystem.pullbackLegComparison (i : Iᵒᵖ) :
    (smallEtalePullbackAb eL).obj ((smallEtalePullbackAb (cT.π.app i)).obj (F.obj i)) ⟶
      (smallEtalePullbackAb (cY.π.app i)).obj ((smallEtalePullbackAb (e.app i)).obj (F.obj i)) :=
  (App eL (cT.π.app i) (cY.π.app i ≫ e.app i) (heL i).symm (F.obj i)).hom ≫
    (App (cY.π.app i) (e.app i) (cY.π.app i ≫ e.app i) rfl (F.obj i)).inv

/-- The comparison `e⁻¹p_i⁻¹ℱ_i ⟶ q_i⁻¹e_i⁻¹ℱ_i` of the projection square is an isomorphism. -/
theorem EtaleSheafSystem.isIso_pullbackLegComparison (i : Iᵒᵖ) :
    IsIso (EtaleSheafSystem.pullbackLegComparison e eL heL F i) := by
  unfold EtaleSheafSystem.pullbackLegComparison
  infer_instance

/-- The comparison of the projection square followed by the leg is the inverse image of the leg
of the presentation on `T`. -/
theorem EtaleSheafSystem.pullbackLegComparison_comp_pullbackLeg
    {𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    EtaleSheafSystem.pullbackLegComparison e eL heL F i ≫
        EtaleSheafSystem.pullbackLeg e eL heL F ι i =
      (smallEtalePullbackAb eL).map (ι i) := by
  unfold EtaleSheafSystem.pullbackLeg EtaleSheafSystem.pullbackLegComparison
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- The correspondence of the transition maps of the two diagrams, with the comparisons of
inverse images written on components. -/
private theorem pullbackDiagramMap_core {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb eL).map
        (App (cT.π.app i) (DT.map a) (cT.π.app j) (cT.w a).symm (F.obj j)).inv ≫
      (smallEtalePullbackAb eL).map ((smallEtalePullbackAb (cT.π.app i)).map
        (EtaleSheafSystem.smallEtaleMap F a)) ≫
      (App eL (cT.π.app i) (cY.π.app i ≫ e.app i) (heL i).symm (F.obj i)).hom ≫
      (App (cY.π.app i) (e.app i) (cY.π.app i ≫ e.app i) rfl (F.obj i)).inv =
    (App eL (cT.π.app j) (cY.π.app j ≫ e.app j) (heL j).symm (F.obj j)).hom ≫
      (App (cY.π.app j) (e.app j) (cY.π.app j ≫ e.app j) rfl (F.obj j)).inv ≫
      (App (cY.π.app i) (DY.map a) (cY.π.app j) (cY.w a).symm
          ((smallEtalePullbackAb (e.app j)).obj (F.obj j))).inv ≫
      (smallEtalePullbackAb (cY.π.app i)).map (EtaleSheafSystem.pullbackMap e F a) := by
  have hnat : DY.map a ≫ e.app j = e.app i ≫ DT.map a := e.naturality a
  have hW₁ : cY.π.app j ≫ e.app j = (cY.π.app i ≫ e.app i) ≫ DT.map a := by
    rw [Category.assoc, ← hnat, ← Category.assoc, cY.w a]
  have hW₂ : cY.π.app j ≫ e.app j = cY.π.app i ≫ (DY.map a ≫ e.app j) := by
    rw [← Category.assoc, cY.w a]
  have hW₃ : cY.π.app j ≫ e.app j = eL ≫ cT.π.app j := (heL j).symm
  have hx := ((smallEtalePullbackAb eL).mapIso
    (App (cT.π.app i) (DT.map a) (cT.π.app j) (cT.w a).symm (F.obj j))).inv_hom_id
  have hn := ((smallEtalePullbackAb (cY.π.app i)).mapIso
    (App (e.app i) (DT.map a) (DY.map a ≫ e.app j) hnat (F.obj j))).inv_hom_id
  have hn' := ((smallEtalePullbackAb (cY.π.app i)).mapIso
    (App (e.app i) (DT.map a) (DY.map a ≫ e.app j) hnat (F.obj j))).hom_inv_id
  have hM : (smallEtalePullbackAb (cY.π.app i)).map (EtaleSheafSystem.pullbackMap e F a) = _ :=
    ((smallEtalePullbackAb (cY.π.app i)).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((smallEtalePullbackAb (cY.π.app i)).map_comp _ _))
  have nE := smallEtalePullbackAbCompApp_hom_naturality eL (cT.π.app i) (cY.π.app i ≫ e.app i)
    (heL i).symm (EtaleSheafSystem.smallEtaleMap F a)
  have nQ := smallEtalePullbackAbCompApp_inv_naturality (cY.π.app i) (e.app i)
    (cY.π.app i ≫ e.app i) rfl (EtaleSheafSystem.smallEtaleMap F a)
  have A₁ := smallEtalePullbackAbCompApp_assoc (cY.π.app i) (e.app i) (DT.map a)
    (cY.π.app i ≫ e.app i) rfl (DY.map a ≫ e.app j) hnat (cY.π.app j ≫ e.app j) hW₁ hW₂ (F.obj j)
  have A₂ := smallEtalePullbackAbCompApp_assoc eL (cT.π.app i) (DT.map a) (cY.π.app i ≫ e.app i)
    (heL i).symm (cT.π.app j) (cT.w a).symm (cY.π.app j ≫ e.app j) hW₁ hW₃ (F.obj j)
  have A₃ := smallEtalePullbackAbCompApp_assoc (cY.π.app i) (DY.map a) (e.app j) (cY.π.app j)
    (cY.w a).symm (DY.map a ≫ e.app j) rfl (cY.π.app j ≫ e.app j) rfl hW₂ (F.obj j)
  exact pullbackDiagramMap_algebra _ _ _ hx _ _ _ nE _ _ _ nQ _ (Iso.inv_hom_id _) _ _ _ A₁
    _ A₂ _ _ (Iso.inv_hom_id _) _ _ (Iso.inv_hom_id _) _ A₃ _ hn hn' _ (Iso.hom_inv_id _) _ hM

/-- **The transition maps of the two diagrams correspond.** The inverse image along `e` of the
transition maps of the diagram `p_i⁻¹ℱ_i` are the transition maps of the diagram
`q_i⁻¹e_i⁻¹ℱ_i` of the inverse image system, under the comparisons of the projection squares. -/
theorem EtaleSheafSystem.pullback_pullbackDiagramMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb eL).map ((conePullbackComp cT a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (cT.π.app i)).map (F.map a)) ≫
      EtaleSheafSystem.pullbackLegComparison e eL heL F i =
    EtaleSheafSystem.pullbackLegComparison e eL heL F j ≫
      (conePullbackComp cY a).inv.app ((EtaleSheafSystem.pullback e F).obj j) ≫
        (smallEtalePullbackAb (cY.π.app i)).map ((EtaleSheafSystem.pullback e F).map a) := by
  rw [conePullbackComp_inv_app_eq, conePullbackComp_inv_app_eq,
    (smallEtalePullbackAb eL).map_comp]
  unfold EtaleSheafSystem.pullbackLegComparison
  simp only [Category.assoc]
  exact pullbackDiagramMap_core e eL heL F a

/-- **The inverse image of a colimit presentation is compatible with the transition maps.** Let
`e : (Y_i) ⟶ (T_i)` be a morphism of inverse systems of schemes, `e : Y ⟶ T` a morphism of cones
over it, and `ι_i : p_i⁻¹ℱ_i ⟶ ℱ` a compatible family on `T`. Then the legs
`q_i⁻¹e_i⁻¹ℱ_i ⟶ e⁻¹ℱ` are compatible with the transition maps of the system `e_i⁻¹ℱ_i`. -/
theorem EtaleSheafSystem.isPullbackCocone_pullback {𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : LimitHigherDirectImage.IsPullbackCocone cT F ι) :
    LimitHigherDirectImage.IsPullbackCocone cY (EtaleSheafSystem.pullback e F)
      (EtaleSheafSystem.pullbackLeg e eL heL F ι) := by
  intro i j a
  have := EtaleSheafSystem.isIso_pullbackLegComparison e eL heL F j
  exact cocone_algebra _ _ _ _ _ (EtaleSheafSystem.pullback_pullbackDiagramMap e eL heL F a) _ _
    _ _ (EtaleSheafSystem.pullbackLegComparison_comp_pullbackLeg e eL heL F ι i)
    (EtaleSheafSystem.pullbackLegComparison_comp_pullbackLeg e eL heL F ι j)
    (by rw [← Functor.map_comp, Category.assoc, hι a]) _ (IsIso.inv_hom_id _)

/-- **The inverse image of a colimit presentation is a colimit presentation**: inverse image is a
left adjoint, so it preserves the colimit `ℱ = colim p_i⁻¹ℱ_i`, and the comparisons of the
projection squares identify the two diagrams. -/
theorem EtaleSheafSystem.isPullbackColimitPresentation_pullback
    {𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation cT 𝓕 F ι) :
    LimitHigherDirectImage.IsPullbackColimitPresentation cY ((smallEtalePullbackAb eL).obj 𝓕)
      (EtaleSheafSystem.pullback e F) (EtaleSheafSystem.pullbackLeg e eL heL F ι) :=
  .of_isSystemColimit <|
  (hpres.isSystemColimit.map_of_isLeftAdjoint (smallEtaleAdjunctionAb eL)).of_isoSystem
    (fun i => @asIso _ _ _ _ (EtaleSheafSystem.pullbackLegComparison e eL heL F i)
      (EtaleSheafSystem.isIso_pullbackLegComparison e eL heL F i)) (Iso.refl _)
    (fun a => EtaleSheafSystem.pullback_pullbackDiagramMap e eL heL F a)
    (fun i => (Category.comp_id _).trans
      (EtaleSheafSystem.pullbackLegComparison_comp_pullbackLeg e eL heL F ι i).symm)

end MorphismOfSystems

end Stacks.EtaleCohomology

end

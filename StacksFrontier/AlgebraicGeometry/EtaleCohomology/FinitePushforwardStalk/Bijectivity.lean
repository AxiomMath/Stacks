module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Injectivity
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Injectivity
import all Mathlib.CategoryTheory.Limits.HasLimits
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Bijectivity of the comparison map for a finite direct image

Étale neighbourhood partitions of the base change of a finite morphism, the surjectivity they
give, and the bijectivity of the comparison map for a finite morphism (Tag 03QP, part (1), for
sheaves of sets), with the resulting product decomposition of the stalk.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

section Bijectivity

private theorem geometricPoint_eq_of_purelyInseparable
    {X Y : Scheme.{u}} (f : X ⟶ Y) {K : Type u} [Field K]
    (g₁ g₂ : Spec (.of K) ⟶ X) (hg : g₁ ≫ f = g₂ ≫ f)
    (hx : g₁ (IsLocalRing.closedPoint K) = g₂ (IsLocalRing.closedPoint K))
    (hf : (f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom.IsPurelyInseparable) :
    g₁ = g₂ := by
  obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp
    congr((Y.SpecToEquivOfField K) $(hg))
  have hc₁ : Y.descResidueField (Scheme.stalkClosedPointTo (g₁ ≫ f)) =
      f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)) ≫
        X.descResidueField (Scheme.stalkClosedPointTo g₁) :=
    Scheme.descResidueField_stalkClosedPointTo_comp f g₁
  have hc₂ : Y.descResidueField (Scheme.stalkClosedPointTo (g₂ ≫ f)) =
      f.residueFieldMap (g₂ (IsLocalRing.closedPoint K)) ≫
        X.descResidueField (Scheme.stalkClosedPointTo g₂) :=
    Scheme.descResidueField_stalkClosedPointTo_comp f g₂
  have h' : f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)) ≫
      X.descResidueField (Scheme.stalkClosedPointTo g₁) =
      (Y.residueFieldCongr e).hom ≫
        f.residueFieldMap (g₂ (IsLocalRing.closedPoint K)) ≫
          X.descResidueField (Scheme.stalkClosedPointTo g₂) :=
    hc₁.symm.trans
      (h.trans (congrArg (fun m => (Y.residueFieldCongr e).hom ≫ m) hc₂))
  have h'' : f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)) ≫
      X.descResidueField (Scheme.stalkClosedPointTo g₁) =
      f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)) ≫
        (X.residueFieldCongr hx).hom ≫
          X.descResidueField (Scheme.stalkClosedPointTo g₂) :=
    h'.trans (f.residueFieldMap_congr'_assoc hx _).symm
  apply (X.SpecToEquivOfField K).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  let x := g₁ (IsLocalRing.closedPoint K)
  algebraize [(f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom]
  refine ⟨hx, CommRingCat.hom_ext ?_⟩
  exact IsPurelyInseparable.injective_comp_algebraMap
    (Y.residueField (f x)) (X.residueField x) _ (CommRingCat.hom_ext_iff.mp h'')

private theorem residueFieldMap_purelyInseparable_of_congr
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) {y : Y} (h : f x = y)
    (hf : ((Y.residueFieldCongr h).inv ≫ f.residueFieldMap x).hom.IsPurelyInseparable) :
    (f.residueFieldMap x).hom.IsPurelyInseparable := by
  subst y
  simpa using hf

open CategoryTheory.Limits in
private theorem exists_etale_partition_subsingleton_geometric_fibers
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : GeometricPoint Y) :
    ∃ (S : Scheme.{u}) (g : S ⟶ Y) (_ : Etale g) (p : y.source ⟶ S)
      (_ : p ≫ g = y.hom) (I : Type) (_ : Finite I)
      (D : I → (pullback f g).Opens),
      Set.PairwiseDisjoint Set.univ (fun i => (D i).1) ∧
      (⋃ i, (D i).1) = Set.univ ∧
      (∀ i, IsClopen (D i).1) ∧
      ∀ i, Subsingleton {h : y.source ⟶ D i //
        h ≫ (D i).ι ≫ pullback.snd f g = p} := by
  classical
  let s : Y := y.hom default
  let Z := f.fiber s
  let _ : Fintype Z := Fintype.ofFinite Z
  let n := Fintype.card Z
  let x : Fin n → Z := (Fintype.equivFin Z).symm
  obtain ⟨U, m, D, v, hdis, hcov, hopen, hpiece, hrest⟩ :=
    AlgebraicGeometry.exists_etaleNeighborhood_purelyInseparable_decomposition
      f n s x (Fintype.equivFin Z).symm.injective (fun _ => isOpen_discrete _)
  obtain ⟨q, hq, hqp⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    U.toBase y.hom U.point U.map_point
  refine ⟨U.scheme, U.toBase, inferInstance, q, hq, Option (Σ i, Fin (m i)),
    inferInstance, D, hdis, hcov, hopen, ?_⟩
  intro i
  refine ⟨fun g₁ g₂ => Subtype.ext ?_⟩
  cases i with
  | none =>
    have he : ((D none).ι ≫ pullback.snd f U.toBase) (g₁.1 default) = U.point := by
      have hg := congrArg (fun a => a default) g₁.2
      exact hg.trans hqp
    have hp : f ((D none).ι ≫ pullback.fst f U.toBase <| g₁.1 default) = s := by
      show (f ∘ ((D none).ι ≫ pullback.fst f U.toBase)) (g₁.1 default) = s
      have hw := congrArg (fun a => a (g₁.1 default))
        (congrArg (fun a => (D none).ι ≫ a) (pullback.condition (f := f) (g := U.toBase)))
      exact hw.trans ((congrArg U.toBase he).trans U.map_point)
    obtain ⟨z, hz⟩ : ((D none).ι ≫ pullback.fst f U.toBase) (g₁.1 default) ∈
        Set.range (f.fiberι s) := by
      rwa [Scheme.Hom.range_fiberι]
    obtain ⟨j, rfl⟩ := (Fintype.equivFin Z).symm.surjective z
    exact False.elim (hrest (g₁.1 default) he j hz.symm)
  | some a =>
    obtain ⟨i, j⟩ := a
    obtain ⟨hfin, hfiber, hmap, hvu, hpure⟩ := hpiece i j
    let π := (D (some ⟨i, j⟩)).ι ≫ pullback.snd f U.toBase
    have hg (g : {g : y.source ⟶ D (some ⟨i, j⟩) // g ≫ π = q}) :
        g.1 default = v i j := by
      have hmem : π (g.1 default) = U.point :=
        (congrArg (fun a => a default) g.2).trans hqp
      exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp hfiber (g.1 default)).mp hmem)
    have hpure' := residueFieldMap_purelyInseparable_of_congr π (v i j) hvu hpure
    have h₁ : g₁.1 (IsLocalRing.closedPoint y.residueField) = v i j :=
      (congrArg (fun z : y.source => g₁.1 z)
        (Subsingleton.elim _ (default : y.source))).trans (hg g₁)
    have h₂ : g₂.1 (IsLocalRing.closedPoint y.residueField) = v i j :=
      (congrArg (fun z : y.source => g₂.1 z)
        (Subsingleton.elim _ (default : y.source))).trans (hg g₂)
    apply geometricPoint_eq_of_purelyInseparable π g₁.1 g₂.1 (g₁.2.trans g₂.2.symm)
    · exact h₁.trans h₂.symm
    · rw [h₁]
      exact hpure'

open CategoryTheory.Limits in
private theorem exists_etale_coprod_lift
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    {K : Type u} [Field K] [IsAlgClosed K]
    {U : Scheme.{u}} (a : U ⟶ X) [Etale a] (p : Spec (.of K) ⟶ U) :
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g)
      (W W' : Scheme.{u}) (e : (W ⨿ W') ≅ pullback f g)
      (h : W ⟶ U) (w : Spec (.of K) ⟶ W),
      h ≫ a = coprod.inl ≫ e.hom ≫ pullback.fst f g ∧ w ≫ h = p := by
  obtain ⟨V, g, hg, W, W', e, h, ha, w, hw⟩ :=
    AlgebraicGeometry.hasPropertyA_of_isIntegralHom f a (p default)
  have : Etale (h ≫ a) := ha.symm ▸ inferInstance
  have : Etale h := Etale.of_comp h a
  obtain ⟨q, hq, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed h p w hw
  exact ⟨V, g, hg, W, W', e, h, q, ha, hq⟩

open Opposite in
private theorem subsingleton_sections_of_isEmpty
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (U : SmallEtale B S hS) [IsEmpty ((SmallEtale.toScheme B S hS).obj U)] :
    Subsingleton (F.obj.obj (op U)) := by
  refine ⟨fun t t' => ?_⟩
  let E : PreZeroHypercover.{u + 1} U :=
    { I₀ := PEmpty.{u + 2}, X := PEmpty.elim, f := fun i => i.elim }
  apply sections_ext_of_etale_covering B S hS F U E _ t t' (fun i => i.elim)
  apply (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
    (E.map (SmallEtale.toScheme B S hS))).2
  exact ⟨fun p => isEmptyElim p, fun i => i.elim⟩

open Opposite in
private theorem exists_section_of_disjoint_cover
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (U : SmallEtale B S hS) (E : PreZeroHypercover.{u + 1} U)
    (hE : (E.map (SmallEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B S hS).obj U))
    [∀ i, Mono (E.f i)]
    (hdis : Pairwise (fun i j => Disjoint
      (Set.range ((SmallEtale.toScheme B S hS).map (E.f i)))
      (Set.range ((SmallEtale.toScheme B S hS).map (E.f j)))))
    (t : ∀ i, F.obj.obj (op (E.X i))) :
    ∃ s : F.obj.obj (op U), ∀ i, F.obj.map (E.f i).op s = t i := by
  let T := SmallEtale.toScheme B S hS
  let t' (i) : PUnit.{u + 2} ⟶ F.obj.obj (op (E.X i)) := ↾fun _ => t i
  obtain ⟨s, hs, _⟩ := F.property.existsUnique_amalgamation_ofArrows E.f
    (smallEtale_generate_covering B S hS U E hE) t' (by
      intro W i j a b hab
      by_cases hij : i = j
      · subst j
        have : a = b := (cancel_mono (E.f i)).mp hab
        subst b
        rfl
      · have : IsEmpty (T.obj W) := ⟨fun w => by
          have he := congrArg (fun k => T.map k w) hab
          simp only [Functor.map_comp, Scheme.Hom.comp_apply] at he
          exact Set.disjoint_left.mp (hdis hij)
            (Set.mem_range_self (T.map a w))
            (he.symm ▸ Set.mem_range_self (T.map b w))⟩
        have := subsingleton_sections_of_isEmpty B S hS F W
        ext w
        exact Subsingleton.elim _ _)
  exact ⟨s PUnit.unit, fun i => ConcreteCategory.congr_hom (hs i) PUnit.unit⟩

/-- Over an étale neighbourhood `g₀` of a geometric point with a lift `q₀`, some basic
neighbourhood of the point maps to `pullback f g₀`, compatibly with the lifts of the point. -/
private theorem exists_lift_to_pullback_of_etale
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)
    {S₀ : Scheme.{u}} (g₀ : S₀ ⟶ Y.1) (hg₀ : Etale g₀) (q₀ : y.source ⟶ S₀)
    (hq₀ : q₀ ≫ g₀ = y.hom) :
    ∃ (V : (geometricPointFiber B Y.1 Y.property y).Elements)
      (r : (SmallEtale.toScheme B X.1 X.property).obj ((smallEtaleBaseChange B f).obj V.1) ⟶
        pullback (B.inclusion.map f) g₀),
      r ≫ pullback.fst _ g₀ = B.inclusion.map (pullback.snd V.1.obj.hom f) ∧
      ∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
        (liftedEtaleNeighborhood B f y x V).2.1 ≫ r ≫ pullback.fst _ g₀ = x.1 ∧
        (liftedEtaleNeighborhood B f y x V).2.1 ≫ r ≫ pullback.snd _ g₀ = q₀ := by
  let N : (Scheme.pointSmallEtale y.hom).fiber.Elements :=
    Functor.elementsMk _ (MorphismProperty.Over.mk _ g₀ hg₀) (Over.homMk q₀ hq₀)
  obtain ⟨V, -, ⟨v⟩⟩ := exists_neighborhood_refinement B Y.1 Y.property y N
  let β : V.1.obj.left.1 ⟶ S₀ := v.1.left
  have hβ : β ≫ g₀ = B.inclusion.map V.1.obj.hom := v.1.w
  have hv : V.2.1 ≫ β = q₀ := congrArg (fun a => a.left) v.2
  let π : ((smallEtaleBaseChange B f).obj V.1).obj.left.1 ⟶ V.1.obj.left.1 :=
    B.inclusion.map (pullback.fst V.1.obj.hom f)
  let ρ : ((smallEtaleBaseChange B f).obj V.1).obj.left.1 ⟶ X.1 :=
    B.inclusion.map (pullback.snd V.1.obj.hom f)
  let P := (IsPullback.of_hasPullback V.1.obj.hom f).map B.inclusion
  refine ⟨V, pullback.lift ρ (π ≫ β) (P.w.symm.trans
    ((congrArg (fun m => π ≫ m) hβ).symm.trans (Category.assoc _ _ _).symm)),
    pullback.lift_fst _ _ _, fun x => ⟨?_, ?_⟩⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => _ ≫ m) (pullback.lift_fst ρ (π ≫ β) _)).trans
        (liftedEtaleNeighborhood B f y x V).2.2)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => _ ≫ m) (pullback.lift_snd ρ (π ≫ β) _)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ β)
            (liftedEtaleNeighborhood_point_fst B f y x V)).trans hv)))

open CategoryTheory.Limits in
private theorem exists_open_neighborhood_lift
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsIntegralHom (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (U : (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements) :
    ∃ (V : (geometricPointFiber B Y.1 Y.property y).Elements)
      (W : (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).Elements)
      (a : W.1 ⟶ (smallEtaleBaseChange B f).obj V.1) (_b : W ⟶ U),
      IsOpenImmersion ((SmallEtale.toScheme B X.1 X.property).map a) ∧
      W.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map a ≫
        B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1 := by
  let f₀ := B.inclusion.map f
  let u := B.inclusion.map U.1.obj.hom
  obtain ⟨V₀, g, hg, W₀, W₀', e, h, w, hhu, hwh⟩ :=
    exists_etale_coprod_lift f₀ u U.2.1
  let k : W₀ ⟶ pullback f₀ g := coprod.inl ≫ e.hom
  let q : y.source ⟶ V₀ := w ≫ k ≫ pullback.snd f₀ g
  have hku : k ≫ pullback.fst f₀ g = h ≫ u := by
    simpa only [k, Category.assoc] using hhu.symm
  have hq : q ≫ g = y.hom := by
    calc
      q ≫ g = w ≫ (k ≫ pullback.fst f₀ g) ≫ f₀ := by
        simp only [q, Category.assoc, pullback.condition]
      _ = (w ≫ h) ≫ u ≫ f₀ := by rw [hku]; simp only [Category.assoc]
      _ = y.hom := by rw [hwh, ← Category.assoc, U.2.2]; exact x.2
  obtain ⟨V, r, hr₁, hr⟩ := exists_lift_to_pullback_of_etale B f y g hg q hq
  let T := (smallEtaleBaseChange B f).obj V.1
  let π : T.obj.left.1 ⟶ V.1.obj.left.1 := B.inclusion.map (pullback.fst V.1.obj.hom f)
  let ρ : T.obj.left.1 ⟶ X.1 := B.inclusion.map (pullback.snd V.1.obj.hom f)
  have hρ : Etale ρ := T.property
  let z : y.source ⟶ T.obj.left.1 := (liftedEtaleNeighborhood B f y x V).2.1
  have hzr : z ≫ r = w ≫ k := by
    refine pullback.hom_ext ?_ ?_
    · refine ((Category.assoc _ _ _).trans (hr x).1).trans ?_
      rw [Category.assoc, hku, ← Category.assoc, hwh]
      exact U.2.2.symm
    · exact ((Category.assoc _ _ _).trans (hr x).2).trans (Category.assoc _ _ _).symm
  let O : T.obj.left.1.Opens := r ⁻¹ᵁ k.opensRange
  have hsize : B.Contains O := (Scheme.size_coe_opens_le _ O).trans_lt T.obj.left.property
  have hO : Set.range z ⊆ Set.range O.ι := by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨z p, ?_⟩, rfl⟩
    show r (z p) ∈ Set.range k
    exact ⟨w p, (congrArg (fun a => a p) hzr).symm⟩
  let z' := IsOpenImmersion.lift O.ι z hO
  have hz' : z' ≫ O.ι = z := IsOpenImmersion.lift_fac _ _ _
  let l : O.toScheme ⟶ W₀ := IsOpenImmersion.lift k (O.ι ≫ r) (by
    rintro _ ⟨p, rfl⟩
    exact p.property)
  have hl : l ≫ k = O.ι ≫ r := IsOpenImmersion.lift_fac _ _ _
  have hzl : z' ≫ l = w := by
    apply (cancel_mono k).mp
    rw [Category.assoc, hl, ← Category.assoc, hz', hzr]
  let Wobj : SmallEtale B X.1 X.property :=
    ⟨Over.mk (ObjectProperty.homMk (O.ι ≫ ρ) : B.obj O hsize ⟶ X), by
      show Etale (O.ι ≫ ρ)
      infer_instance⟩
  let W : (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements :=
    Functor.elementsMk _ Wobj ⟨z', by
      show z' ≫ (O.ι ≫ ρ) = x.1
      rw [← Category.assoc, hz']
      exact (liftedEtaleNeighborhood B f y x V).2.2⟩
  let a : W.1 ⟶ T := ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk O.ι) rfl)
  have hlh : (l ≫ h) ≫ u = O.ι ≫ ρ := by
    rw [Category.assoc, ← hku, ← Category.assoc, hl, Category.assoc, hr₁]
    rfl
  let b : W ⟶ U :=
    ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (l ≫ h))
      (by apply ObjectProperty.hom_ext; exact hlh)), by
      apply Subtype.ext
      show z' ≫ (l ≫ h) = U.2.1
      rw [← Category.assoc, hzl, hwh]⟩
  refine ⟨V, W, a, b, inferInstanceAs (IsOpenImmersion O.ι), ?_⟩
  show z' ≫ O.ι ≫ π = V.2.1
  rw [← Category.assoc, hz']
  exact liftedEtaleNeighborhood_point_fst B f y x V

open CategoryTheory.Limits in
private theorem liftedEtaleNeighborhood_map_point
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (y : GeometricPoint Y.1)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    {V V' : (geometricPointFiber B Y.1 Y.property y).Elements}
    (a : V' ⟶ V) :
    (liftedEtaleNeighborhood B f y x V').2.1 ≫
      (SmallEtale.toScheme B X.1 X.property).map
        ((smallEtaleBaseChange B f).map a.1) =
      (liftedEtaleNeighborhood B f y x V).2.1 := by
  let T := SmallEtale.toScheme B X.1 X.property
  let z' := (liftedEtaleNeighborhood B f y x V').2.1
  let c := T.map ((smallEtaleBaseChange B f).map a.1)
  have hfst0 : ((Over.pullback f).map a.1.hom).left ≫ pullback.fst V.1.obj.hom f =
      pullback.fst V'.1.obj.hom f ≫ a.1.hom.left := pullback.lift_fst _ _ _
  have hsnd0 : ((Over.pullback f).map a.1.hom).left ≫ pullback.snd V.1.obj.hom f =
      pullback.snd V'.1.obj.hom f := pullback.lift_snd _ _ _
  have hfst : c ≫ B.inclusion.map (pullback.fst V.1.obj.hom f) =
      B.inclusion.map (pullback.fst V'.1.obj.hom f) ≫
        (SmallEtale.toScheme B Y.1 Y.property).map a.1 :=
    (B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map hfst0).trans (B.inclusion.map_comp _ _))
  have hsnd : c ≫ B.inclusion.map (pullback.snd V.1.obj.hom f) =
      B.inclusion.map (pullback.snd V'.1.obj.hom f) :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map hsnd0)
  refine ((IsPullback.of_hasPullback V.1.obj.hom f).map B.inclusion).hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => z' ≫ m) hfst).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ (SmallEtale.toScheme B Y.1 Y.property).map a.1)
              (liftedEtaleNeighborhood_point_fst B f y x V')).trans
            ((congrArg Subtype.val a.2).trans
              (liftedEtaleNeighborhood_point_fst B f y x V).symm))))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => z' ≫ m) hsnd).trans
        ((liftedEtaleNeighborhood B f y x V').2.2.trans
          (liftedEtaleNeighborhood B f y x V).2.2.symm))

private theorem exists_common_neighborhood
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) {I : Type*} [Finite I]
    (U : I → (geometricPointFiber B S hS s).Elements) :
    ∃ V : (geometricPointFiber B S hS s).Elements, ∀ i, Nonempty (V ⟶ U i) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  obtain ⟨V, hV⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image U)
  exact ⟨V, fun i => hV (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

open CategoryTheory.Limits in
private theorem exists_disjoint_opens_over_geometric_lifts
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1) :
    ∃ (V : (geometricPointFiber B Y.1 Y.property y).Elements)
      (O : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom} →
        ((SmallEtale.toScheme B X.1 X.property).obj
          ((smallEtaleBaseChange B f).obj V.1)).Opens),
      (∀ x, (liftedEtaleNeighborhood B f y x V).2.1 default ∈ O x) ∧
      Pairwise (fun x x' => Disjoint (O x).1 (O x').1) := by
  classical
  let f₀ := B.inclusion.map f
  obtain ⟨S₀, g₀, hg₀, q₀, hq₀, I, hI, D, hdis, hcov, hopen, hsingle⟩ :=
    exists_etale_partition_subsingleton_geometric_fibers f₀ y
  obtain ⟨V, r, -, hr⟩ := exists_lift_to_pullback_of_etale B f y g₀ hg₀ q₀ hq₀
  let q (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :=
    (liftedEtaleNeighborhood B f y x V).2.1 ≫ r
  have hq₁ (x) : q x ≫ pullback.fst f₀ g₀ = x.1 := (Category.assoc _ _ _).trans (hr x).1
  have hq₂ (x) : q x ≫ pullback.snd f₀ g₀ = q₀ := (Category.assoc _ _ _).trans (hr x).2
  have hmem (x) : ∃ i, q x default ∈ D i := by
    have := Set.eq_univ_iff_forall.mp hcov (q x default)
    exact Set.mem_iUnion.mp this
  choose i hi using hmem
  have hii : Function.Injective i := by
    intro x x' hxx
    have hmem' : Set.range (q x') ⊆ Set.range (D (i x)).ι := by
      rintro _ ⟨p, rfl⟩
      refine ⟨⟨q x' p, ?_⟩, rfl⟩
      rw [Subsingleton.elim p (default : y.source), hxx]
      exact hi x'
    have hmem : Set.range (q x) ⊆ Set.range (D (i x)).ι := by
      rintro _ ⟨p, rfl⟩
      refine ⟨⟨q x p, ?_⟩, rfl⟩
      rw [Subsingleton.elim p (default : y.source)]
      exact hi x
    let p := IsOpenImmersion.lift (D (i x)).ι (q x) hmem
    let p' := IsOpenImmersion.lift (D (i x)).ι (q x') hmem'
    have hp : p ≫ (D (i x)).ι = q x := IsOpenImmersion.lift_fac _ _ _
    have hp' : p' ≫ (D (i x)).ι = q x' := IsOpenImmersion.lift_fac _ _ _
    have e := (hsingle (i x)).elim
      (⟨p, by rw [← Category.assoc, hp, hq₂]⟩ :
        {g : y.source ⟶ D (i x) //
          g ≫ (D (i x)).ι ≫ pullback.snd f₀ g₀ = q₀})
      ⟨p', by rw [← Category.assoc, hp', hq₂]⟩
    have ep : p = p' := congrArg Subtype.val e
    apply Subtype.ext
    rw [← hq₁ x, ← hq₁ x', ← hp, ← hp', ep]
  refine ⟨V, fun x => r ⁻¹ᵁ D (i x), hi, fun x x' hxx => Set.disjoint_left.mpr fun p hp hp' =>
    Set.disjoint_left.mp
      (hdis (Set.mem_univ _) (Set.mem_univ _) (fun h => hxx (hii h))) hp hp'⟩

private theorem smallEtale_map_structure
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : SmallEtale B S hS} (a : U ⟶ V) :
    (SmallEtale.toScheme B S hS).map a ≫ B.inclusion.map V.obj.hom =
      B.inclusion.map U.obj.hom := by
  show B.inclusion.map a.hom.left ≫ _ = _
  rw [← Functor.map_comp]
  exact congrArg B.inclusion.map (Over.w a.hom)

/-- A point of a neighbourhood mapping to the base point over a base change `V` is the
canonical lift of that point. -/
private theorem point_comp_map_eq_liftedEtaleNeighborhood
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (y : GeometricPoint Y.1)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    {V : (geometricPointFiber B Y.1 Y.property y).Elements}
    {W : (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements}
    (a : W.1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (ha : W.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1) :
    W.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map a =
      (liftedEtaleNeighborhood B f y x V).2.1 := by
  apply ((IsPullback.of_hasPullback V.1.obj.hom f).map B.inclusion).hom_ext
  · exact (Category.assoc _ _ _).trans
      (ha.trans (liftedEtaleNeighborhood_point_fst B f y x V).symm)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => W.2.1 ≫ m) (smallEtale_map_structure B X.1 X.property a)).trans
        (W.2.2.trans (liftedEtaleNeighborhood B f y x V).2.2.symm))

open CategoryTheory.Limits in
private structure EtaleNeighborhoodPartition
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (y : GeometricPoint Y.1)
    (U : ∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
      (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).Elements) where
  base : (geometricPointFiber B Y.1 Y.property y).Elements
  neighborhood : ∀ x, (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map f) y x)).Elements
  toBase : ∀ x, (neighborhood x).1 ⟶ (smallEtaleBaseChange B f).obj base.1
  toNeighborhood : ∀ x, neighborhood x ⟶ U x
  point_toBase : ∀ x, (neighborhood x).2.1 ≫
    (SmallEtale.toScheme B X.1 X.property).map (toBase x) ≫
      B.inclusion.map (pullback.fst base.1.obj.hom f) = base.2.1
  mono_toBase : ∀ x, Mono (toBase x)
  covers : ∀ p : (SmallEtale.toScheme B X.1 X.property).obj
      ((smallEtaleBaseChange B f).obj base.1),
    ∃ x, p ∈ Set.range ((SmallEtale.toScheme B X.1 X.property).map (toBase x))
  disjoint : Pairwise (fun x x' => Disjoint
    (Set.range ((SmallEtale.toScheme B X.1 X.property).map (toBase x)))
    (Set.range ((SmallEtale.toScheme B X.1 X.property).map (toBase x'))))

open CategoryTheory.Limits in
private theorem exists_partition_of_disjoint_neighborhoods
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (U : ∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
      (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).Elements)
    (V : (geometricPointFiber B Y.1 Y.property y).Elements)
    (W : ∀ x, (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements)
    (a : ∀ x, (W x).1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (b : ∀ x, W x ⟶ U x)
    (ha : ∀ x, (W x).2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map (a x) ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1)
    [∀ x, Mono (a x)]
    (hdis : Pairwise (fun x x' => Disjoint
      (Set.range ((SmallEtale.toScheme B X.1 X.property).map (a x)))
      (Set.range ((SmallEtale.toScheme B X.1 X.property).map (a x'))))) :
    Nonempty (EtaleNeighborhoodPartition B f y U) := by
  let T := SmallEtale.toScheme B X.1 X.property
  have he (x) : Etale (T.map (a x)) := etale_smallEtale_map B X.1 X.property _
  have hpoint (x) := point_comp_map_eq_liftedEtaleNeighborhood B f y x (a x) (ha x)
  let O : (T.obj ((smallEtaleBaseChange B f).obj V.1)).Opens :=
    ⟨⋃ x, Set.range (T.map (a x)), isOpen_iUnion fun x => (T.map (a x)).isOpenMap.isOpen_range⟩
  obtain ⟨V', c, hc⟩ := exists_baseChange_refinement_range_subset B f y V O fun x =>
    Set.mem_iUnion.mpr ⟨x, (W x).2.1 default, congrArg (fun p => p default) (hpoint x)⟩
  let d := (smallEtaleBaseChange B f).map c.1
  let W' (x) := pullback (a x) d
  let P (x) := (IsPullback.of_hasPullback (a x) d).map T
  let q (x) : y.source ⟶ T.obj (W' x) := (P x).lift (W x).2.1
    (liftedEtaleNeighborhood B f y x V').2.1
    ((hpoint x).trans (liftedEtaleNeighborhood_map_point B f y x c).symm)
  have hq₁ (x) : q x ≫ T.map (pullback.fst (a x) d) = (W x).2.1 :=
    (P x).lift_fst _ _ _
  have hq₂ (x) : q x ≫ T.map (pullback.snd (a x) d) =
      (liftedEtaleNeighborhood B f y x V').2.1 := (P x).lift_snd _ _ _
  let N (x) : (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements :=
    Functor.elementsMk _ (W' x) ⟨q x, by
      have h : T.map (pullback.fst (a x) d) ≫ B.inclusion.map (W x).1.obj.hom =
          B.inclusion.map (W' x).obj.hom := by
        show B.inclusion.map (pullback.fst (a x) d).hom.left ≫ _ = _
        rw [← Functor.map_comp, Over.w]
      rw [← h, ← Category.assoc, hq₁]
      exact (W x).2.2⟩
  let b' (x) : N x ⟶ W x := ⟨pullback.fst (a x) d, Subtype.ext (hq₁ x)⟩
  refine ⟨{
    base := V'
    neighborhood := N
    toBase := fun x => pullback.snd (a x) d
    toNeighborhood := fun x => b' x ≫ b x
    point_toBase := ?_
    mono_toBase := fun x => inferInstance
    covers := ?_
    disjoint := ?_ }⟩
  · intro x
    rw [← Category.assoc, hq₂]
    exact liftedEtaleNeighborhood_point_fst B f y x V'
  · intro p
    obtain ⟨x, w, hw⟩ := Set.mem_iUnion.mp (hc (Set.mem_range_self p))
    obtain ⟨p', _, hp'⟩ := Scheme.exists_preimage_of_isPullback (P x) w p hw
    exact ⟨x, p', hp'⟩
  · intro x x' hxx
    apply Set.disjoint_left.mpr
    rintro p ⟨w, rfl⟩ ⟨w', hw'⟩
    apply Set.disjoint_left.mp (hdis hxx)
      (Set.mem_range_self (T.map (pullback.fst (a x) d) w))
    refine ⟨T.map (pullback.fst (a x') d) w', ?_⟩
    have h₁ := congrArg (fun k => T.map k w) (pullback.condition (f := a x) (g := d))
    have h₂ := congrArg (fun k => T.map k w') (pullback.condition (f := a x') (g := d))
    simp only [Functor.map_comp, Scheme.Hom.comp_apply] at h₁ h₂
    exact h₂.trans ((congrArg (T.map d) hw').trans h₁.symm)

open CategoryTheory.Limits Opposite in
private theorem finitePushforwardStalkComponent_surjective_of_partitions
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (h : ∀ U, Nonempty (EtaleNeighborhoodPartition B f y U)) :
    Function.Surjective (fun z x => finitePushforwardStalkComponent B f y F x z) := by
  classical
  intro t
  let D (x) := (CategoryOfElements.π (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj
  have hrep (x) := Types.jointly_surjective_of_isColimit (colimit.isColimit (D x)) (t x)
  choose U s hs using hrep
  let Q := Classical.choice (h fun x => (U x).unop)
  let L := {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}
  let E : PreZeroHypercover.{u + 1} ((smallEtaleBaseChange B f).obj Q.base.1) :=
    { I₀ := ULift.{u + 1} L, X := fun x => (Q.neighborhood x.down).1,
      f := fun x => Q.toBase x.down }
  have hE : (E.map (SmallEtale.toScheme B X.1 X.property)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B X.1 X.property).obj
        ((smallEtaleBaseChange B f).obj Q.base.1)) := by
    refine (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) _).2
      ⟨fun p => ?_, fun x => etale_smallEtale_map B X.1 X.property _⟩
    obtain ⟨x, hx⟩ := Q.covers p
    exact ⟨⟨x⟩, hx⟩
  have hmono (i : E.I₀) : Mono (E.f i) := Q.mono_toBase i.down
  obtain ⟨s', hs'⟩ := exists_section_of_disjoint_cover B X.1 X.property F _ E hE
    (fun i j hij => Q.disjoint (fun he => hij (ULift.ext he)))
    (fun i => F.obj.map (Q.toNeighborhood i.down).1.op (s i.down))
  let D' := (CategoryOfElements.π
    (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj
  refine ⟨colimit.ι D' (op Q.base) s', funext fun x => ?_⟩
  refine (finitePushforwardStalkComponent_germ_of_hom B f y F x
    (Q.neighborhood x) Q.base (Q.toBase x) (Q.point_toBase x) s').trans ?_
  rw [hs' ⟨x⟩]
  show colimit.ι (D x) (op (Q.neighborhood x))
      ((D x).map (Q.toNeighborhood x).op (s x)) = t x
  rw [← ConcreteCategory.comp_apply, colimit.w]
  exact hs x

open CategoryTheory.Limits in
private theorem exists_etaleNeighborhoodPartition
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
    [Finite {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}]
    (U : ∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
      (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).Elements) :
    Nonempty (EtaleNeighborhoodPartition B f y U) := by
  classical
  obtain ⟨V₀, O₀, hp₀, hd₀⟩ := exists_disjoint_opens_over_geometric_lifts B f y
  have hl (x) := exists_open_neighborhood_lift B f y x (U x)
  choose Vx Wx ax bx hax hpx using hl
  let L := {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}
  let Vs : Option L → (geometricPointFiber B Y.1 Y.property y).Elements :=
    fun i => i.elim V₀ Vx
  obtain ⟨V, hc⟩ := exists_common_neighborhood B Y.1 Y.property y Vs
  let c (i : Option L) : V ⟶ Vs i := Classical.choice (hc i)
  let T := SmallEtale.toScheme B X.1 X.property
  let C := smallEtaleBaseChange B f
  let r₀ := T.map (C.map (c none).1)
  let r (x) := T.map (C.map (c (some x)).1)
  let z (x) := (liftedEtaleNeighborhood B f y x V).2.1
  have hz₀ (x) : z x ≫ r₀ = (liftedEtaleNeighborhood B f y x V₀).2.1 :=
    liftedEtaleNeighborhood_map_point B f y x (c none)
  have hz (x) : z x ≫ r x = (Wx x).2.1 ≫ T.map (ax x) := by
    have hz' : z x ≫ r x = (liftedEtaleNeighborhood B f y x (Vx x)).2.1 :=
      liftedEtaleNeighborhood_map_point B f y x (c (some x))
    exact hz'.trans (point_comp_map_eq_liftedEtaleNeighborhood B f y x (ax x) (hpx x)).symm
  let O (x) : (T.obj (C.obj V.1)).Opens :=
    (r₀ ⁻¹ᵁ O₀ x) ⊓ (r x ⁻¹ᵁ (T.map (ax x)).opensRange)
  have hO (x) : Set.range (z x) ⊆ Set.range (O x).ι := by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨z x p, ?_, ?_⟩, rfl⟩
    · have he := congrArg (fun a => a p) (hz₀ x)
      show r₀ (z x p) ∈ O₀ x
      change r₀ (z x p) = (liftedEtaleNeighborhood B f y x V₀).2.1 p at he
      rw [he, Subsingleton.elim p (default : y.source)]
      exact hp₀ x
    · exact ⟨(Wx x).2.1 p, (congrArg (fun a => a p) (hz x)).symm⟩
  let p (x) := IsOpenImmersion.lift (O x).ι (z x) (hO x)
  have hp (x) : p x ≫ (O x).ι = z x := IsOpenImmersion.lift_fac _ _ _
  let l (x) : (O x).toScheme ⟶ T.obj (Wx x).1 :=
    IsOpenImmersion.lift (T.map (ax x)) ((O x).ι ≫ r x) (by
      rintro _ ⟨q, rfl⟩
      exact q.property.2)
  have hla (x) : l x ≫ T.map (ax x) = (O x).ι ≫ r x :=
    IsOpenImmersion.lift_fac _ _ _
  have hpl (x) : p x ≫ l x = (Wx x).2.1 := by
    refine (cancel_mono (T.map (ax x))).mp ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => p x ≫ m) (hla x)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ r x) (hp x)).trans (hz x))))
  let ρ := B.inclusion.map (C.obj V.1).obj.hom
  have hρ : Etale ρ := (C.obj V.1).property
  let hsize (x) : B.Contains (O x) :=
    (Scheme.size_coe_opens_le _ (O x)).trans_lt (C.obj V.1).obj.left.property
  let Nobj (x) : SmallEtale B X.1 X.property :=
    ⟨Over.mk (ObjectProperty.homMk ((O x).ι ≫ ρ) : B.obj (O x) (hsize x) ⟶ X), by
      show Etale ((O x).ι ≫ ρ)
      infer_instance⟩
  let N (x) : (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements :=
    Functor.elementsMk _ (Nobj x) ⟨p x, by
      show p x ≫ ((O x).ι ≫ ρ) = x.1
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ ρ) (hp x)).trans
          (liftedEtaleNeighborhood B f y x V).2.2)⟩
  let a (x) : (N x).1 ⟶ C.obj V.1 :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (O x).ι) rfl)
  have hlw (x) : l x ≫ B.inclusion.map (Wx x).1.obj.hom = (O x).ι ≫ ρ :=
    (congrArg (fun m => l x ≫ m)
        (smallEtale_map_structure B X.1 X.property (ax x)).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ B.inclusion.map
            ((smallEtaleBaseChange B f).obj (Vx x).1).obj.hom) (hla x)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun k => (O x).ι ≫ k)
              (smallEtale_map_structure B X.1 X.property (C.map (c (some x)).1))))))
  let b (x) : N x ⟶ Wx x :=
    ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (l x))
      (by apply ObjectProperty.hom_ext; exact hlw x)), Subtype.ext (hpl x)⟩
  have hm (x) : Mono (a x) := by
    apply T.mono_of_mono_map
    show Mono (O x).ι
    infer_instance
  apply exists_partition_of_disjoint_neighborhoods B f y U V N a (fun x => b x ≫ bx x)
  · intro x
    show p x ≫ (O x).ι ≫ _ = V.2.1
    rw [← Category.assoc, hp]
    exact liftedEtaleNeighborhood_point_fst B f y x V
  · intro x x' hxx
    apply Set.disjoint_left.mpr
    rintro q ⟨p, rfl⟩ ⟨p', he⟩
    apply Set.disjoint_left.mp (hd₀ hxx) p.property.1
    show r₀ ((O x).ι p) ∈ O₀ x'
    change (O x').ι p' = (O x).ι p at he
    rw [← he]
    exact p'.property.1


/-- **Stacks Project, Tag 03QP, part (1), sheaves of sets.** For a finite morphism the
comparison map from the stalk of a direct image to the product of the stalks over the lifts of
the geometric point is bijective. -/
@[stacks 03QP "part (1): the stalk of a finite pushforward, for sheaves of sets"]
public theorem finitePushforwardStalkToProduct_bijective
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    Function.Bijective (finitePushforwardStalkToProduct B f y F) := by
  classical
  have hdef : finitePushforwardStalkToProduct B f y F =
      fun z x => finitePushforwardStalkComponent B f y F x z := rfl
  rw [hdef]
  refine ⟨finitePushforwardStalkComponent_injective B f y F, ?_⟩
  exact finitePushforwardStalkComponent_surjective_of_partitions B f y F
    (exists_etaleNeighborhoodPartition B f y)

/-- **Stacks Project, Tag 03QP, part (1), sheaves of sets.** The stalk at a geometric point `y`
of the direct image of a sheaf of sets along a finite morphism is the product of the stalks of
the sheaf over the lifts of `y`. -/
@[stacks 03QP "part (1): the stalk of a finite pushforward, for sheaves of sets",
  sga "4 VIII 5.5" "partial"]
public def finitePushforwardStalkEquiv
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj ≃
      (∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
        etaleStalk B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x) F.obj) :=
  finitePushforwardStalkEquivOfBijective B f y F
    (finitePushforwardStalkToProduct_bijective B f y F)

/-- **Stacks Project, Tag 03QP, part (1), sheaves of sets.** Each component of the product
decomposition of the stalk is the canonical stalk map at the corresponding lift. -/
@[stacks 03QP "part (1): the stalk of a finite pushforward, for sheaves of sets"]
public theorem finitePushforwardStalkEquiv_apply
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (z : etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    finitePushforwardStalkEquiv B f y F z x =
      finitePushforwardStalkComponent B f y F x z :=
  rfl

/-- The product decomposition of the stalk is natural in the sheaf. -/
public theorem finitePushforwardStalkEquiv_natural
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
    {F G : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))} (α : F ⟶ G)
    (z : etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    finitePushforwardStalkEquiv B f y G
        ((etaleStalkFunctor.{u, u + 1} B Y.1 Y.property y).map
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).map α) z) x =
      (etaleStalkFunctor.{u, u + 1} B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).map α
        (finitePushforwardStalkEquiv B f y F z x) :=
  finitePushforwardStalkToProduct_natural B f y α z x

end Bijectivity

end AlgebraicGeometry

end

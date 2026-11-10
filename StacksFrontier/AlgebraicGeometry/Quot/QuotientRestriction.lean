module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleCoveringEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RefinementFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Restriction of quotients of an inverse image along a morphism over the base

Let `F` be an `𝒪_A`-module on an algebraic space `A` and let `π : W ⟶ A` be a morphism of
algebraic spaces, so that `π^*F` is a module on `W`.  A quotient of `π^*F` is recorded, as in
Stacks 082M, by its kernel, a subobject of `π^*F`.  Given a morphism `a : W' ⟶ W` and a
morphism `π' : W' ⟶ A` with `a ≫ π = π'`, a quotient `π^*F ⟶ Q` restricts to the quotient
`π'^*F ≅ a^*π^*F ⟶ a^*Q` of `π'^*F`.

## Main definitions

* `AlgebraicGeometry.Space.quotientRestrictAlong`: the restriction of a quotient of `π^*F` along a
  morphism over `A`.

## Main results

* `AlgebraicGeometry.Space.quotientRestrictAlong_comp`: restriction is compatible with composition,
  by the pseudofunctoriality of the inverse images of Stacks 03LU.
* `AlgebraicGeometry.Space.quotientRestrictAlong_injective_of_isFlat`: along a flat surjective
  morphism restriction of quotients is injective.

## References

* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The modules here have their sections in the universe `u` of the schemes; the ambient-universe
-- abelian structure of the cohomology of modules would be selected ahead of
-- `SheafOfModules.instAbelian` and leave the module universe of every subobject unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace CategoryTheory.Functor

variable {C D₀ D₁ D₂ : Type*} [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]
  [Abelian D₁] [Abelian D₂]

/-- **Two conjugates of two quotients that agree give an isomorphism of the images of the
quotients, intertwining the images of the projections through a comparison of the further
functors.**  Here `P₁ ≅ P₀ ⋙ L₁` and `P₁' ≅ P₀ ⋙ L₁'` present `P₁` and `P₁'` as images of `P₀`,
the conjugations along `La` and `Lb` are compared by `κ : L₁ ⋙ La ≅ L₁' ⋙ Lb`, and `H` says that
the comparisons are coherent. -/
theorem exists_iso_comp_eq_of_conjSubobject_eq {D₁' : Type*} [Category* D₁'] [Abelian D₁']
    {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₁' : C ⥤ D₁'} {P₂ : C ⥤ D₂}
    {L₁ : D₀ ⥤ D₁} {L₁' : D₀ ⥤ D₁'} {La : D₁ ⥤ D₂} {Lb : D₁' ⥤ D₂}
    [La.PreservesEpimorphisms] [Lb.PreservesEpimorphisms]
    (c₁ : P₁ ≅ P₀ ⋙ L₁) (c₁' : P₁' ≅ P₀ ⋙ L₁') (ca : P₂ ≅ P₁ ⋙ La) (cb : P₂ ≅ P₁' ⋙ Lb)
    (κ : L₁ ⋙ La ≅ L₁' ⋙ Lb)
    (H : ca ≪≫ isoWhiskerRight c₁ La ≪≫ associator P₀ L₁ La ≪≫ isoWhiskerLeft P₀ κ =
      cb ≪≫ isoWhiskerRight c₁' Lb ≪≫ associator P₀ L₁' Lb)
    {M : C} (K : Subobject (P₁.obj M)) (K' : Subobject (P₁'.obj M))
    (hK : conjSubobject ca K = conjSubobject cb K') :
    ∃ ι : La.obj (cokernel K.arrow) ≅ Lb.obj (cokernel K'.arrow),
      La.map (c₁.inv.app M ≫ cokernel.π K.arrow : L₁.obj (P₀.obj M) ⟶ cokernel K.arrow) ≫
          ι.hom =
        (κ.hom.app (P₀.obj M) : La.obj (L₁.obj (P₀.obj M)) ⟶ Lb.obj (L₁'.obj (P₀.obj M))) ≫
          Lb.map (c₁'.inv.app M ≫ cokernel.π K'.arrow :
            L₁'.obj (P₀.obj M) ⟶ cokernel K'.arrow) := by
  obtain ⟨ι, hι⟩ := Abelian.exists_iso_of_kernelSubobject_eq (conjQuotientProjection ca K)
    (conjQuotientProjection cb K') hK
  refine ⟨ι, ?_⟩
  have hH := congrArg (fun φ => φ.hom.app M) H
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    associator_hom_app, isoWhiskerLeft_hom, whiskerLeft_app, Category.id_comp] at hH
  simp only [conjQuotientProjection] at hι
  have hκ : κ.hom.app (P₀.obj M) = La.map (c₁.inv.app M) ≫ ca.inv.app M ≫ cb.hom.app M ≫
      Lb.map (c₁'.hom.app M) := by
    rw [← cancel_epi (ca.hom.app M ≫ La.map (c₁.hom.app M)), Category.assoc, hH]
    simp [← Functor.map_comp_assoc]
  rw [hκ, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp]
  rw [← hι]
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Restriction

variable {A W W' W'' : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS A.1 A.2)

/-- **The restriction of a quotient of `π^*F` along a morphism over the base.**  For
`a : W' ⟶ W` with `a ≫ π = π'`, the quotient `π'^*F ≅ a^*π^*F ⟶ a^*(π^*F / K)` of `π'^*F`,
recorded by its kernel. -/
def quotientRestrictAlong {π : W ⟶ A} {π' : W' ⟶ A} (a : W' ⟶ W) (ha : a ≫ π = π')
    (K : Subobject ((modulePullback B S hS π).obj F)) :
    Subobject ((modulePullback B S hS π').obj F) :=
  Functor.conjSubobject (modulePullbackTriangle B S hS ha) K

/-- The quotient by a restricted quotient is the inverse image of the quotient. -/
def quotientRestrictAlongCokernelIso {π : W ⟶ A} {π' : W' ⟶ A} (a : W' ⟶ W) (ha : a ≫ π = π')
    (K : Subobject ((modulePullback B S hS π).obj F)) :
    cokernel (quotientRestrictAlong F a ha K).arrow ≅
      (modulePullback B S hS a).obj (cokernel K.arrow) :=
  Functor.conjSubobjectCokernelIso (modulePullbackTriangle B S hS ha) K

/-- The restriction depends on the morphism only, not on the proof that it lies over `A`. -/
theorem quotientRestrictAlong_congr {π : W ⟶ A} {π' : W' ⟶ A} {a b : W' ⟶ W} (hab : a = b)
    (ha : a ≫ π = π') (hb : b ≫ π = π') (K : Subobject ((modulePullback B S hS π).obj F)) :
    quotientRestrictAlong F a ha K = quotientRestrictAlong F b hb K := by
  subst hab
  rfl

/-- **Restriction of quotients is compatible with composition.** -/
theorem quotientRestrictAlong_comp (hc : ModulePushforwardCoherence B S hS) {π : W ⟶ A}
    {π' : W' ⟶ A} {π'' : W'' ⟶ A} (a : W'' ⟶ W') (b : W' ⟶ W) (ha : a ≫ π' = π'')
    (hb : b ≫ π = π') (hab : (a ≫ b) ≫ π = π'')
    (K : Subobject ((modulePullback B S hS π).obj F)) :
    quotientRestrictAlong F (a ≫ b) hab K =
      quotientRestrictAlong F a ha (quotientRestrictAlong F b hb K) :=
  Functor.conjSubobject_comp (modulePullbackTriangle B S hS hb)
    (modulePullbackTriangle B S hS ha) (modulePullbackTriangle B S hS hab)
    (modulePullbackTriangle B S hS (rfl : a ≫ b = a ≫ b))
    (hc.modulePullbackTriangle_comp' rfl hb ha hab) K

set_option synthInstance.maxHeartbeats 400000 in
-- instance search over categories of sheaves of modules on algebraic spaces (subobjects, cokernels)
/-- **Restriction of quotients along a morphism whose inverse image reflects vanishing is
injective.** -/
theorem quotientRestrictAlong_injective_of_reflects {π : W ⟶ A} {π' : W' ⟶ A} (a : W' ⟶ W)
    (ha : a ≫ π = π')
    (hrefl : ∀ {M N : Modules.{u, u} B S hS W.1 W.2} (v : M ⟶ N),
      (modulePullback B S hS a).map v = 0 → v = 0) :
    Function.Injective (quotientRestrictAlong F a ha) := by
  have := (modulePullbackAdjunction B S hS a).isLeftAdjoint
  have key : ∀ K₁ K₂ : Subobject ((modulePullback B S hS π).obj F),
      quotientRestrictAlong F a ha K₁ = quotientRestrictAlong F a ha K₂ → K₁ ≤ K₂ := by
    intro K₁ K₂ h
    set e := modulePullbackTriangle B S hS ha
    have hz : K₁.arrow ≫ cokernel.π K₂.arrow = 0 := by
      refine hrefl _ ?_
      set x := (modulePullback B S hS a).map K₁.arrow ≫ e.inv.app F
      have h₁ : x ≫ Functor.conjQuotientProjection e K₁ = 0 := by
        simp only [x, Functor.conjQuotientProjection, Category.assoc, Iso.inv_hom_id_app_assoc]
        rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
      have h₂ : x ≫ Functor.conjQuotientProjection e K₂ = 0 := by
        have h' : kernelSubobject (Functor.conjQuotientProjection e K₁) =
            kernelSubobject (Functor.conjQuotientProjection e K₂) := h
        exact (kernelSubobject_factors_iff _ _).1 (h' ▸ (kernelSubobject_factors_iff _ _).2 h₁)
      simpa [x, Functor.conjQuotientProjection, Category.assoc] using h₂
    calc K₁ ≤ kernelSubobject (cokernel.π K₂.arrow) := le_kernelSubobject _ _ hz
      _ = K₂ := kernelSubobject_cokernel_π K₂
  intro K₁ K₂ h
  exact le_antisymm (key K₁ K₂ h) (key K₂ K₁ h.symm)

end Restriction

section Glue

open QuasiCoherentDescent

variable {A W Y' P : AlgebraicSpaces B S hS}

/-- **The comparisons of inverse images along two legs with equal composites are coherent with
the canonical comparison of Stacks 04W5.**  For `a : P ⟶ Y` and `b : P ⟶ Y'` with
`a ≫ j = b ≫ j'`, reading `r^*` as the inverse image along `a` of `πY^* ≅ πW^* ⋙ j^*` and
comparing the two legs by the canonical comparison is the same as reading it along `b`. -/
theorem modulePullbackTriangle_trans_canonicalComparisonIso
    (hc : ModulePushforwardCoherence B S hS) {Y : AlgebraicSpaces B S hS} {πW : W ⟶ A}
    {πY : Y ⟶ A} {πY' : Y' ⟶ A} {r : P ⟶ A} (j : Y ⟶ W) (j' : Y' ⟶ W) (a : P ⟶ Y) (b : P ⟶ Y')
    (hj : j ≫ πW = πY) (hj' : j' ≫ πW = πY') (ha : a ≫ πY = r) (hb : b ≫ πY' = r)
    (hab : a ≫ j = b ≫ j') :
    modulePullbackTriangle B S hS ha ≪≫
        Functor.isoWhiskerRight (modulePullbackTriangle B S hS hj) (modulePullback B S hS a) ≪≫
        Functor.associator (modulePullback B S hS πW) (modulePullback B S hS j)
          (modulePullback B S hS a) ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS πW)
          (canonicalComparisonIso B S hS a b j j' hab) =
      modulePullbackTriangle B S hS hb ≪≫
        Functor.isoWhiskerRight (modulePullbackTriangle B S hS hj') (modulePullback B S hS b) ≪≫
        Functor.associator (modulePullback B S hS πW) (modulePullback B S hS j')
          (modulePullback B S hS b) := by
  have hka : (a ≫ j) ≫ πW = r := by rw [Category.assoc, hj, ha]
  have hkb : (b ≫ j') ≫ πW = r := by rw [Category.assoc, hj', hb]
  have e₁ := hc.modulePullbackTriangle_comp (rfl : a ≫ j = a ≫ j) hj ha hka
  have e₂ := hc.modulePullbackTriangle_comp (rfl : b ≫ j' = b ≫ j') hj' hb hkb
  have e₃ := modulePullbackTriangle_congr_left hab hka hkb
  have e₄ : modulePullbackTriangle B S hS (rfl : a ≫ j = a ≫ j) ≪≫
      canonicalComparisonIso B S hS a b j j' hab =
      eqToIso (congrArg (modulePullback B S hS) hab) ≪≫
        modulePullbackTriangle B S hS (rfl : b ≫ j' = b ≫ j') := by
    rw [modulePullbackTriangle_rfl, modulePullbackTriangle_rfl, canonicalComparisonIso,
      Iso.symm_self_id_assoc]
  calc _ = (modulePullbackTriangle B S hS ha ≪≫
        Functor.isoWhiskerRight (modulePullbackTriangle B S hS hj) (modulePullback B S hS a) ≪≫
        Functor.associator (modulePullback B S hS πW) (modulePullback B S hS j)
          (modulePullback B S hS a)) ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS πW)
          (canonicalComparisonIso B S hS a b j j' hab) := by simp only [Iso.trans_assoc]
    _ = modulePullbackTriangle B S hS hka ≪≫ Functor.isoWhiskerLeft (modulePullback B S hS πW)
          (modulePullbackTriangle B S hS (rfl : a ≫ j = a ≫ j) ≪≫
            canonicalComparisonIso B S hS a b j j' hab) := by
        rw [← e₁, Functor.isoWhiskerLeft_trans, Iso.trans_assoc]
    _ = modulePullbackTriangle B S hS hkb ≪≫ Functor.isoWhiskerLeft (modulePullback B S hS πW)
          (modulePullbackTriangle B S hS (rfl : b ≫ j' = b ≫ j')) := by
        rw [e₄, e₃, Functor.isoWhiskerLeft_trans, Iso.trans_assoc, ← Iso.trans_assoc
          (Functor.isoWhiskerLeft _ _) (Functor.isoWhiskerLeft _ _),
          ← Functor.isoWhiskerLeft_trans, eqToIso_trans, eqToIso_refl,
          Functor.isoWhiskerLeft_refl, Iso.refl_trans]
    _ = _ := by rw [e₂]

/-- The projection of `j^*πW^*F` onto a quotient of `πY^*F`, for `j ≫ πW = πY`. -/
def descentProjection (F : Modules.{u, u} B S hS A.1 A.2) {πW : W ⟶ A} {πY : Y' ⟶ A}
    (j : Y' ⟶ W) (hj : j ≫ πW = πY)
    (K : Subobject ((modulePullback B S hS πY).obj F)) :
    (modulePullback B S hS j).obj ((modulePullback B S hS πW).obj F) ⟶ cokernel K.arrow :=
  (modulePullbackTriangle B S hS hj).inv.app F ≫ cokernel.π K.arrow

/-- The projection `descentProjection F j hj K` is an epimorphism. -/
instance (F : Modules.{u, u} B S hS A.1 A.2) {πW : W ⟶ A} {πY : Y' ⟶ A} (j : Y' ⟶ W)
    (hj : j ≫ πW = πY)
    (K : Subobject ((modulePullback B S hS πY).obj F)) :
    Epi (descentProjection F j hj K) :=
  epi_comp' (IsIso.epi_of_iso ((modulePullbackTriangle B S hS hj).app F).inv) inferInstance

variable {I : Type*} (Yi : I → AlgebraicSpaces B S hS) (fi : ∀ i, Yi i ⟶ W)

/-- The second projection of a pairwise fibre product of a family over `W` lies over `A` through
the first one. -/
theorem pairSnd_comp_eq {πW : W ⟶ A} {πY : ∀ i, Yi i ⟶ A} (hj : ∀ i, fi i ≫ πW = πY i)
    (i i' : I) :
    pairSnd B S hS Yi fi i i' ≫ πY i' = pairFst B S hS Yi fi i i' ≫ πY i := by
  rw [← hj i, ← hj i', ← Category.assoc, ← Category.assoc, pair_condition B S hS Yi fi i i']

/-- **The cocycle condition of Stacks 04W3 for a quotient of a canonical descent datum.**  A
family of modules on the members of a family over `W` with pairwise isomorphisms, receiving
epimorphisms from the inverse images of one quasi-coherent module `M` which intertwine the
pairwise isomorphisms with the canonical comparisons, satisfies the cocycle condition: it is
inherited from that of the canonical descent datum of `M`. -/
theorem transitionOn_cocycle_of_epi (M : Modules.{u, u} B S hS W.1 W.2)
    (_hM : M.IsQuasicoherentOnSite) (G : ∀ i, Modules.{u, u} B S hS (Yi i).1 (Yi i).2)
    (χ : ∀ i i', (modulePullback B S hS (pairFst B S hS Yi fi i i')).obj (G i) ≅
      (modulePullback B S hS (pairSnd B S hS Yi fi i i')).obj (G i'))
    (q : ∀ i, (modulePullback B S hS (fi i)).obj M ⟶ G i) [∀ i, Epi (q i)]
    (hnat : ∀ i i', (modulePullback B S hS (pairFst B S hS Yi fi i i')).map (q i) ≫
        (χ i i').hom =
      (canonicalComparison (pairFst B S hS Yi fi i i') (pairSnd B S hS Yi fi i i') (fi i)
        (fi i') (pair_condition B S hS Yi fi i i') M).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi fi i i')).map (q i'))
    (i i' k : I) (T : AlgebraicSpaces B S hS)
    (vi : T ⟶ Yi i) (vj : T ⟶ Yi i') (vk : T ⟶ Yi k)
    (vij : T ⟶ pair B S hS Yi fi i i') (vjk : T ⟶ pair B S hS Yi fi i' k)
    (vik : T ⟶ pair B S hS Yi fi i k)
    (hij₀ : vij ≫ pairFst B S hS Yi fi i i' = vi) (hij₁ : vij ≫ pairSnd B S hS Yi fi i i' = vj)
    (hjk₀ : vjk ≫ pairFst B S hS Yi fi i' k = vj) (hjk₁ : vjk ≫ pairSnd B S hS Yi fi i' k = vk)
    (hik₀ : vik ≫ pairFst B S hS Yi fi i k = vi) (hik₁ : vik ≫ pairSnd B S hS Yi fi i k = vk) :
    transitionOn B S hS Yi fi G χ i i' vij vi vj hij₀ hij₁ ≪≫
        transitionOn B S hS Yi fi G χ i' k vjk vj vk hjk₀ hjk₁ =
      transitionOn B S hS Yi fi G χ i k vik vi vk hik₀ hik₁ := by
  have n := fun (s t : I) (v : T ⟶ pair B S hS Yi fi s t) (vs : T ⟶ Yi s) (vt : T ⟶ Yi t)
      (hs : v ≫ pairFst B S hS Yi fi s t = vs) (ht : v ≫ pairSnd B S hS Yi fi s t = vt) =>
    transitionOn_naturality_of_pairwise B S hS Yi fi
      (fun i => (modulePullback B S hS (fi i)).obj M) G
      (fun s t => canonicalComparison (pairFst B S hS Yi fi s t) (pairSnd B S hS Yi fi s t)
        (fi s) (fi t) (pair_condition B S hS Yi fi s t) M) χ q hnat s t v vs vt hs ht
  have e := fun (s t : I) (v : T ⟶ pair B S hS Yi fi s t) (vs : T ⟶ Yi s) (vt : T ⟶ Yi t)
      (hs : v ≫ pairFst B S hS Yi fi s t = vs) (ht : v ≫ pairSnd B S hS Yi fi s t = vt) =>
    transitionOn_canonicalComparison B S hS Yi fi M s t v vs vt hs ht
  have cocM := (congrArg₂ (· ≪≫ ·) (e i i' vij vi vj hij₀ hij₁) (e i' k vjk vj vk hjk₀ hjk₁)).trans
    ((canonicalComparison_trans B S hS vi vj vk (fi i) (fi i') (fi k) _ _ M).trans
      (e i k vik vi vk hik₀ hik₁).symm)
  apply Iso.ext
  refine (cancel_epi ((modulePullback B S hS vi).map (q i))).1 ?_
  calc _ = ((modulePullback B S hS vi).map (q i) ≫
          (transitionOn B S hS Yi fi G χ i i' vij vi vj hij₀ hij₁).hom) ≫
          (transitionOn B S hS Yi fi G χ i' k vjk vj vk hjk₀ hjk₁).hom :=
        (Category.assoc _ _ _).symm
    _ = _ := by
      rw [n i i' vij vi vj hij₀ hij₁, Category.assoc, n i' k vjk vj vk hjk₀ hjk₁,
        ← Category.assoc]
      rfl
    _ = _ := congrArg (· ≫ (modulePullback B S hS vk).map (q k)) (congrArg Iso.hom cocM)
    _ = _ := (n i k vik vi vk hik₀ hik₁).symm

/-- The descent datum of Stacks 04W3 carried by a family of quotients of the inverse images of
one quasi-coherent module, with pairwise isomorphisms intertwined with the canonical
comparisons. -/
def descentDatumOfEpi (M : Modules.{u, u} B S hS W.1 W.2) (hM : M.IsQuasicoherentOnSite)
    (G : ∀ i, Modules.{u, u} B S hS (Yi i).1 (Yi i).2) (hG : ∀ i, (G i).IsQuasicoherentOnSite)
    (χ : ∀ i i', (modulePullback B S hS (pairFst B S hS Yi fi i i')).obj (G i) ≅
      (modulePullback B S hS (pairSnd B S hS Yi fi i i')).obj (G i'))
    (q : ∀ i, (modulePullback B S hS (fi i)).obj M ⟶ G i) [∀ i, Epi (q i)]
    (hnat : ∀ i i', (modulePullback B S hS (pairFst B S hS Yi fi i i')).map (q i) ≫
        (χ i i').hom =
      (canonicalComparison (pairFst B S hS Yi fi i i') (pairSnd B S hS Yi fi i i') (fi i)
        (fi i') (pair_condition B S hS Yi fi i i') M).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi fi i i')).map (q i')) :
    DescentDatum B S hS Yi fi where
  F := G
  quasicoherent := hG
  transition := χ
  cocycle := transitionOn_cocycle_of_epi Yi fi M hM G χ q hnat

/-- **An epimorphism onto the components of a descent datum descends.**  Let `D` be a descent
datum of Stacks 04W3 relative to an étale covering `(fi i : Yi i ⟶ W)`, and let
`q i : (fi i)^*M ⟶ D.F i` be epimorphisms from the inverse images of one quasi-coherent
`𝒪_W`-module `M`, intertwining the canonical comparisons of `M` with the pairwise isomorphisms of
`D`.  Then `D` is the canonical descent datum of a quasi-coherent `Q`, and the `q i` are the
inverse images of one epimorphism `M ⟶ Q`. -/
theorem exists_epi_of_descentDatum
    (M : Modules.{u, u} B S hS W.1 W.2) (hM : M.IsQuasicoherentOnSite)
    (G : ∀ i, Modules.{u, u} B S hS (Yi i).1 (Yi i).2) (hG : ∀ i, (G i).IsQuasicoherentOnSite)
    (χ : ∀ i i', (modulePullback B S hS (pairFst B S hS Yi fi i i')).obj (G i) ≅
      (modulePullback B S hS (pairSnd B S hS Yi fi i i')).obj (G i'))
    (q : ∀ i, (modulePullback B S hS (fi i)).obj M ⟶ G i) [∀ i, Epi (q i)]
    (hnat : ∀ i i', (modulePullback B S hS (pairFst B S hS Yi fi i i')).map (q i) ≫
        (χ i i').hom =
      (canonicalComparison (pairFst B S hS Yi fi i i') (pairSnd B S hS Yi fi i i') (fi i)
        (fi i') (pair_condition B S hS Yi fi i i') M).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi fi i i')).map (q i'))
    (hje : ∀ i, IsEtale B S hS (fi i).hom)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (fi i).hom)) :
    ∃ (Q : Modules.{u, u} B S hS W.1 W.2) (_ : Q.IsQuasicoherentOnSite) (φ : M ⟶ Q)
      (θ : ∀ i, G i ≅ (modulePullback B S hS (fi i)).obj Q),
      Epi φ ∧ ∀ i, q i ≫ (θ i).hom = (modulePullback B S hS (fi i)).map φ := by
  obtain ⟨Q, hQ, ⟨θ⟩⟩ := isEffective_of_isEtaleCovering B S hS Yi fi hje hcov
    (descentDatumOfEpi Yi fi M hM G hG χ q hnat)
  let θi : ∀ i, G i ≅ (modulePullback B S hS (fi i)).obj Q := fun i =>
    { hom := (θ.hom.app i : G i ⟶ (modulePullback B S hS (fi i)).obj Q)
      inv := (θ.inv.app i : (modulePullback B S hS (fi i)).obj Q ⟶ G i)
      hom_inv_id := congrArg (DescentDatum.Hom.app · i) θ.hom_inv_id
      inv_hom_id := congrArg (DescentDatum.Hom.app · i) θ.inv_hom_id }
  have hθ : ∀ i i', (modulePullback B S hS (pairFst B S hS Yi fi i i')).map (θi i).hom ≫
      (canonicalComparison (pairFst B S hS Yi fi i i') (pairSnd B S hS Yi fi i i') (fi i)
        (fi i') (pair_condition B S hS Yi fi i i') Q).hom =
      (χ i i').hom ≫ (modulePullback B S hS (pairSnd B S hS Yi fi i i')).map (θi i').hom :=
    fun i i' => θ.hom.naturality i i'
  have hΦ : ∀ i i', (modulePullback B S hS (pairFst B S hS Yi fi i i')).map (q i ≫ (θi i).hom) ≫
      (canonicalComparison (pairFst B S hS Yi fi i i') (pairSnd B S hS Yi fi i i') (fi i)
        (fi i') (pair_condition B S hS Yi fi i i') Q).hom =
      (canonicalComparison (pairFst B S hS Yi fi i i') (pairSnd B S hS Yi fi i i') (fi i)
        (fi i') (pair_condition B S hS Yi fi i i') M).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi fi i i')).map (q i' ≫ (θi i').hom) := by
    intro i i'
    rw [Functor.map_comp, Category.assoc, hθ, ← Category.assoc, hnat, Category.assoc,
      Functor.map_comp]
  let Φ : canonicalDescentDatum' B S hS Yi fi M hM ⟶ canonicalDescentDatum' B S hS Yi fi Q hQ :=
    { app := fun i => q i ≫ (θi i).hom
      naturality := hΦ }
  obtain ⟨hff⟩ := nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering B S hS Yi fi
    (isFpqcCovering_of_isEtaleCovering B S hS _ _ hcov)
  let φ := hff.preimage (X := ⟨M, hM⟩) (Y := ⟨Q, hQ⟩) Φ
  have hφ : ∀ i, (modulePullback B S hS (fi i)).map φ.hom = q i ≫ (θi i).hom := fun i =>
    congrArg (DescentDatum.Hom.app · i) (hff.map_preimage (X := ⟨M, hM⟩) (Y := ⟨Q, hQ⟩) Φ)
  refine ⟨Q, hQ, φ.hom, θi, ?_, fun i => (hφ i).symm⟩
  refine epi_of_forall_epi_modulePullback_map_of_isFlat B S hS fi
    (fun i => isFlat_of_isEtale B S hS (hje i)) hcov.jointly_surjective φ.hom fun i => ?_
  rw [hφ i]
  have : IsIso (θi i).hom := Iso.isIso_hom (θi i)
  exact epi_comp' inferInstance (IsIso.epi_of_iso (θi i).hom)

/-- The pairwise isomorphisms of the descent datum of a compatible family of quotients. -/
theorem exists_quotientTransition (hc : ModulePushforwardCoherence B S hS)
    (F : Modules.{u, u} B S hS A.1 A.2) {πW : W ⟶ A}
    {πY : ∀ i, Yi i ⟶ A} (hj : ∀ i, fi i ≫ πW = πY i)
    (K' : ∀ i, Subobject ((modulePullback B S hS (πY i)).obj F))
    (hcomp : ∀ i i', quotientRestrictAlong F (pairFst B S hS Yi fi i i') rfl (K' i) =
      quotientRestrictAlong F (pairSnd B S hS Yi fi i i') (pairSnd_comp_eq Yi fi hj i i') (K' i'))
    (i i' : I) :
    ∃ ι : (modulePullback B S hS (pairFst B S hS Yi fi i i')).obj (cokernel (K' i).arrow) ≅
        (modulePullback B S hS (pairSnd B S hS Yi fi i i')).obj (cokernel (K' i').arrow),
      (modulePullback B S hS (pairFst B S hS Yi fi i i')).map
          (descentProjection F (fi i) (hj i) (K' i)) ≫ ι.hom =
        (canonicalComparison (pairFst B S hS Yi fi i i') (pairSnd B S hS Yi fi i i') (fi i)
          (fi i') (pair_condition B S hS Yi fi i i') ((modulePullback B S hS πW).obj F)).hom ≫
          (modulePullback B S hS (pairSnd B S hS Yi fi i i')).map
            (descentProjection F (fi i') (hj i') (K' i')) := by
  obtain ⟨ι, hι⟩ := Functor.exists_iso_comp_eq_of_conjSubobject_eq
    (modulePullbackTriangle B S hS (hj i)) (modulePullbackTriangle B S hS (hj i'))
    (modulePullbackTriangle B S hS (rfl : pairFst B S hS Yi fi i i' ≫ πY i = _))
    (modulePullbackTriangle B S hS (pairSnd_comp_eq Yi fi hj i i'))
    (canonicalComparisonIso B S hS (pairFst B S hS Yi fi i i') (pairSnd B S hS Yi fi i i')
      (fi i) (fi i') (pair_condition B S hS Yi fi i i'))
    (modulePullbackTriangle_trans_canonicalComparisonIso hc (fi i) (fi i') _ _ (hj i) (hj i')
      rfl (pairSnd_comp_eq Yi fi hj i i') (pair_condition B S hS Yi fi i i'))
    (K' i) (K' i') (hcomp i i')
  refine ⟨ι, ?_⟩
  rwa [← Iso.app_hom, canonicalComparisonIso_app] at hι

/-- **Descent of quasi-coherent quotients along an étale covering.**  Let `(fi i : Yi i ⟶ W)` be
an étale covering lying over `A` through `πW` and the `πY i`, and let `F` be a quasi-coherent
`𝒪_A`-module.  A family of quasi-coherent quotients of the `πY i^*F` whose restrictions to the
pairwise fibre products agree is the family of restrictions of one quasi-coherent quotient of
`πW^*F`. -/
theorem exists_quotientRestrictAlong_eq_of_isEtaleCovering (hc : ModulePushforwardCoherence B S hS)
    (F : Modules.{u, u} B S hS A.1 A.2) (hF : F.IsQuasicoherentOnSite) {πW : W ⟶ A}
    {πY : ∀ i, Yi i ⟶ A} (hj : ∀ i, fi i ≫ πW = πY i) (hje : ∀ i, IsEtale B S hS (fi i).hom)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (fi i).hom))
    (K' : ∀ i, Subobject ((modulePullback B S hS (πY i)).obj F))
    (hK' : ∀ i, (cokernel (K' i).arrow).IsQuasicoherentOnSite)
    (hcomp : ∀ i i', quotientRestrictAlong F (pairFst B S hS Yi fi i i') rfl (K' i) =
      quotientRestrictAlong F (pairSnd B S hS Yi fi i i') (pairSnd_comp_eq Yi fi hj i i') (K' i')) :
    ∃ K : Subobject ((modulePullback B S hS πW).obj F),
      (∀ i, quotientRestrictAlong F (fi i) (hj i) K = K' i) ∧
        (cokernel K.arrow).IsQuasicoherentOnSite := by
  choose ι hι using exists_quotientTransition Yi fi hc F hj K' hcomp
  obtain ⟨Q, hQ, φ, θ, hφ, hθ⟩ := exists_epi_of_descentDatum Yi fi _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS πW F hF)
    (fun i => cokernel (K' i).arrow) hK' ι
    (fun i => descentProjection F (fi i) (hj i) (K' i)) hι hje hcov
  refine ⟨kernelSubobject φ, fun i => ?_, ?_⟩
  · refine (Functor.conjSubobject_kernelSubobject_eq (modulePullbackTriangle B S hS (hj i))
      φ (cokernel.π (K' i).arrow) (θ i).symm ?_).trans (kernelSubobject_cokernel_π (K' i))
    rw [← hθ i, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      descentProjection, Iso.hom_inv_id_app_assoc]
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (Abelian.cokernelKernelSubobjectIso φ).symm hQ

end Glue

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinOpenness
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackTowerExistence
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStackFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatAlgebraizationExists
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# Towers of quotients over square-zero towers: algebraization, morphisms, surjectivity

Inputs for the effectivity of towers of quotients in `Quot_{F/X/S}` (axiom [5] of Stacks 0CZW):

* `AlgebraicGeometry.Space.QuotSituation.exists_tower_algebraization`: the quotient modules of a
  compatible tower of quotients over the levels of a square-zero tower algebraize to one coherent
  module over the limit (Grothendieck existence for such towers, Stacks 0CXB);
* `AlgebraicGeometry.Space.QuotSituation.exists_hom_of_tower`: a compatible family of morphisms
  `F_n ⟶ G_n` over the levels comes from one morphism over the limit (representability of `Hom`
  sheaves, Stacks 08K6, and the affine points over a tower cocone);
* `AlgebraicGeometry.Space.epi_of_epi_modulePullback_of_surjective`: surjectivity of a morphism of
  quasi-coherent modules with target of finite type can be checked after pullback along a morphism
  surjective on points;
* `AlgebraicGeometry.Space.QuotSituation.exists_quotient_of_tower_of_algebraization`: the core
  statement, from an algebraization of the quotient modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

variable {C D₀ D₁ D₂ : Type*} [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]

/-- The transition of a family of maps out of a tower of base changes: a map `P₁ M ⟶ g N` read
through `c₀ : P₂ ≅ P₁ ⋙ t` and the comparison `tri : k ≅ g ⋙ t`. -/
def conjTransition {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {g : D₀ ⥤ D₁} {t : D₁ ⥤ D₂} {k : D₀ ⥤ D₂}
    (c₀ : P₂ ≅ P₁ ⋙ t) (tri : k ≅ g ⋙ t) {M : C} {N : D₀} (φ₁ : P₁.obj M ⟶ g.obj N) :
    P₂.obj M ⟶ k.obj N :=
  conjMap c₀ φ₁ ≫ tri.inv.app N

/-- A map `P₂ M ⟶ L Q` read back through a comparison `e : P₂ ≅ P₁ ⋙ L` as a map
`L (P₁ M) ⟶ L Q`. -/
def conjInv {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M : C} {Q : D₁}
    (φ : P₂.obj M ⟶ L.obj Q) : L.obj (P₁.obj M) ⟶ L.obj Q :=
  e.inv.app M ≫ φ

/-- A transition of a compatible family of maps out of a tower of base changes, read through the
comparisons, as a conjugation. -/
theorem conjHom_inv_app_comp_eq {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {g : D₀ ⥤ D₁}
    {t : D₁ ⥤ D₂} {k : D₀ ⥤ D₂} (tri : k ≅ g ⋙ t) (c₁ : P₁ ≅ P₀ ⋙ g) (c₀ : P₂ ≅ P₁ ⋙ t)
    (c : P₂ ≅ P₀ ⋙ k)
    (hfac : c ≪≫ isoWhiskerLeft P₀ tri = c₀ ≪≫ isoWhiskerRight c₁ t ≪≫ associator P₀ g t)
    {M : C} {N : D₀} (φ₁ : P₁.obj M ⟶ g.obj N) (φ₀ : P₂.obj M ⟶ k.obj N)
    (hφ : conjTransition c₀ tri φ₁ = φ₀) :
    conjHom tri (conjInv c₁ φ₁) = conjInv c φ₀ := by
  have key := NatTrans.congr_app (congrArg Iso.hom hfac) M
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app, associator_hom_app, Category.comp_id] at key
  subst hφ
  unfold conjTransition conjInv
  have key' : tri.hom.app (P₀.obj M) ≫ t.map (c₁.inv.app M) = c.inv.app M ≫ c₀.hom.app M := by
    rw [← cancel_epi (c.hom.app M), Iso.hom_inv_id_app_assoc, reassoc_of% key,
      ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, Category.comp_id]
  simp only [conjHom, conjMap, Functor.map_comp, ← Category.assoc, key']

/-- A transition of a family of maps into the restrictions of a module, built from isomorphisms
`ψ₁`, `ψ₂` compatible with a pinned fibre map. -/
theorem conjTransition_comp_inv_eq {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {g : D₀ ⥤ D₁} {t : D₁ ⥤ D₂}
    {k : D₀ ⥤ D₂} (c₀ : P₂ ≅ P₁ ⋙ t) (tri : k ≅ g ⋙ t) {M : C} {N : D₀} {Q₁ : D₁} {Q₂ : D₂}
    (π₁ : P₁.obj M ⟶ Q₁) (π₂ : P₂.obj M ⟶ Q₂) (fib : t.obj Q₁ ⟶ Q₂)
    (hpin : conjMap c₀ π₁ ≫ fib = π₂) (ψ₁ : g.obj N ≅ Q₁) (ψ₂ : k.obj N ≅ Q₂)
    (hψ : fibreComp tri fib ψ₁.hom = ψ₂.hom) :
    conjTransition c₀ tri (π₁ ≫ ψ₁.inv) = π₂ ≫ ψ₂.inv := by
  have key : t.map ψ₁.inv ≫ tri.inv.app N = fib ≫ ψ₂.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, ← hψ, fibreComp, Iso.inv_hom_id_app_assoc,
      ← t.map_comp_assoc, Iso.inv_hom_id, t.map_id, Category.id_comp]
  subst hpin
  simp only [conjTransition, conjMap, Functor.map_comp, Category.assoc, key]

/-- **The conjugate of the kernel of an epimorphism is the given quotient.** If the image of an
epimorphism `u : P₁ M ⟶ Q` under `L`, read through `e`, is the projection onto the quotient by
`K` followed by an isomorphism, the conjugate of the kernel subobject of `u` is `K`. -/
theorem conjSubobject_kernelSubobject [Abelian D₁] [Abelian D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L : D₁ ⥤ D₂} [L.PreservesEpimorphisms] (e : P₂ ≅ P₁ ⋙ L) {M : C} {Q : D₁}
    (u : P₁.obj M ⟶ Q) [Epi u] (K : Subobject (P₂.obj M)) (ψ : L.obj Q ≅ cokernel K.arrow)
    (h : L.map u = conjInv e (cokernel.π K.arrow ≫ ψ.inv)) :
    conjSubobject e (kernelSubobject u) = K := by
  have hcomp : conjQuotientProjection e (kernelSubobject u) ≫
      L.map (Abelian.cokernelKernelSubobjectIso u).hom ≫ ψ.hom = cokernel.π K.arrow := by
    rw [conjQuotientProjection, Category.assoc, ← L.map_comp_assoc,
      ← Abelian.cokernelKernelSubobjectIso_inv_comp u, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, h, conjInv]
    simp
  rw [conjSubobject, ← kernelSubobject_cokernel_π K, ← hcomp]
  exact (kernelSubobject_comp_mono _ _).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

/- The inverse image of modules is never unfolded below: comparisons of inverse images along
definitionally equal morphisms then proceed argument by argument. -/
attribute [local irreducible] modulePullback

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The module comparison of a composite of morphisms of `Coh_{X/Y}`**, read off an equation
`m ≫ ⟨b₁, ψ₁⟩ = ⟨b₀, ψ₀⟩`. -/
theorem CoherentSituation.fibre_eq_of_comp_eq (D' : CoherentSituation B S hS)
    {A₀ A₁ A : CoherentObject D'} (m : CoherentHom A₀ A₁) {b₁ : A₁.T ⟶ A.T} {b₀ : A₀.T ⟶ A.T}
    (ψ₁ : (modulePullback B S hS (D'.relativeMap b₁)).obj A.F ≅ A₁.F)
    (ψ₀ : (modulePullback B S hS (D'.relativeMap b₀)).obj A.F ≅ A₀.F)
    (h : m.comp ⟨b₁, ψ₁.hom, Iso.isIso_hom _⟩ = ⟨b₀, ψ₀.hom, Iso.isIso_hom _⟩)
    (hw : D'.relativeMap m.base ≫ D'.relativeMap b₁ = D'.relativeMap b₀) :
    Functor.fibreComp (modulePullbackTriangle B S hS hw) m.fibre ψ₁.hom = ψ₀.hom := by
  have h' : (⟨m.base ≫ b₁, Functor.fibreComp (D'.compComparison m.base b₁) m.fibre ψ₁.hom,
      Functor.isIso_fibreComp _ _ _⟩ : CoherentHom A₀ A) =
      ⟨b₀, ψ₀.hom, Iso.isIso_hom _⟩ := h
  obtain ⟨hb, hf⟩ := CoherentHom.mk.inj h'
  subst hb
  exact eq_of_heq hf

/-- **A map of quasi-coherent modules, with target of finite type, is surjective as soon as its
inverse image along a morphism surjective on points is.** The support of the cokernel pulls back
to the support of the inverse image of the cokernel, which is empty. -/
theorem epi_of_epi_modulePullback_of_surjective {X X₀ : AlgebraicSpaces B S hS} (j : X₀ ⟶ X)
    (hj : Function.Surjective (pointsMap B S hS X₀.1 j.hom))
    {M N : Modules.{u, u} B S hS X.1 X.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (hNft : SheafOfModules.IsFiniteTypeOnSite N) (u : M ⟶ N)
    (hu : Epi ((modulePullback B S hS j).map u)) : Epi u := by
  have hQqc : (cokernel u).IsQuasicoherentOnSite :=
    @isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 M N hM hN u
  have hQft := isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS X.1 X.2 u hNft
  have hadj := modulePullbackAdjunction B S hS j
  have := hadj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS j) :=
    hadj.leftAdjoint_preservesColimits
  have hQ0 : IsZero ((modulePullback B S hS j).obj (cokernel u)) :=
    ((Preadditive.epi_iff_isZero_cokernel _).mp hu).of_iso
      (PreservesCokernel.iso (modulePullback B S hS j) u)
  have hpre := supportOfSheaf_modulePullback_eq B S hS j _ hQqc hQft
  rw [(supportOfSheaf_eq_empty_iff_isZero B S hS X₀ _).2 hQ0] at hpre
  rw [Preadditive.epi_iff_isZero_cokernel]
  refine (supportOfSheaf_eq_empty_iff_isZero B S hS X _).mp
    (Set.eq_empty_of_forall_notMem fun x hx => ?_)
  obtain ⟨w, rfl⟩ := hj x
  exact (Set.eq_empty_iff_forall_notMem.1 hpre.symm w) hx

namespace QuotSituation

variable (D : QuotSituation B S hS) (ι : ∀ T : BigFppfOver B S hS,
    (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
  [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]

/-- A leg of a cocone as a morphism of test schemes over the base. -/
def legHom {T : ℕ ⥤ BigFppfOver B S hS} (c : Cocone T) (n : ℕ) :
    D.testOver ι (T.obj n) ⟶ D.testOver ι c.pt :=
  D.testHom ι (c.ι.app n)

/-- The tower of objects of `Coh_{X/Y}` attached to a compatible tower of quotients. -/
abbrev towerCoherentStep {T : ℕ ⥤ BigFppfOver B S hS}
    (K : ∀ n, D.properlySupportedQuotients (D.testOver ι (T.obj n)))
    (hK : ∀ n, D.quotientPullback (D.testHom ι (T.map (homOfLE (n.le_add_right 1))))
      (K (n + 1)).1 = (K n).1) (n : ℕ) :
    CoherentHom (D.cohObject _ (K n).1 (K n).2) (D.cohObject _ (K (n + 1)).1 (K (n + 1)).2) :=
  ⟨D.testHom ι (T.map (homOfLE (n.le_add_right 1))), D.cohFibreOfEq _ (hK n),
    D.isIso_cohFibreOfEq _ (hK n)⟩

/-- The module comparison of a step of the tower is pinned by the two projections. -/
theorem towerCoherentStep_isPinned {T : ℕ ⥤ BigFppfOver B S hS}
    (K : ∀ n, D.properlySupportedQuotients (D.testOver ι (T.obj n)))
    (hK : ∀ n, D.quotientPullback (D.testHom ι (T.map (homOfLE (n.le_add_right 1))))
      (K (n + 1)).1 = (K n).1) (n : ℕ) :
    Functor.conjMap (D.toCoherentSituation.presentationComparison
        (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))))
        (D.presentation _ (K (n + 1)).1) ≫ D.cohFibreOfEq _ (hK n) =
      D.presentation _ (K n).1 :=
  D.isPinned_cohFibreOfEq _ (hK n)

/-- The morphism of test schemes over the base attached to a composite is the composite. -/
theorem testHom_comp {T T' T'' : BigFppfOver B S hS} (g : T ⟶ T') (g' : T' ⟶ T'') :
    D.testHom ι (g ≫ g') = D.testHom ι g ≫ D.testHom ι g' :=
  CostructuredArrow.hom_ext _ _ rfl

include ι in
/-- **Algebraization of a tower of quotients** (Grothendieck existence for towers, Stacks 0CXB).
If `f` is separated, the quotient modules of a compatible tower of quotients over the levels of a
square-zero tower of affine test schemes with limit `c.pt` algebraize: there is a quasi-coherent
module `G` of finite presentation on the base change to `c.pt`, flat over `c.pt` and properly
supported, with isomorphisms `ψ n` from its restrictions to the quotient modules, compatible with
the steps of the tower as morphisms of `Coh_{X/Y}`. -/
theorem exists_tower_algebraization (hsep : IsSeparated B S hS D.f.hom)
    {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ} {cR : Cone R} (hcR : IsLimit cR)
    (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
    (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), (RingHom.ker (R.map f).hom.toRingHom) ^ 2 = ⊥)
    {T : ℕ ⥤ BigFppfOver B S hS} {c : Cocone T}
    {e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (T.obj n) ≅ Spec (.of (R.obj (.op n)))}
    {eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt)}
    (he : ∀ {i j : ℕ} (f : i ⟶ j),
      (BigFppfOver.toScheme B S hS).map (T.map f) ≫ (e j).hom =
        (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
    (heL : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
      (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)
    (K : ∀ n, D.properlySupportedQuotients (D.testOver ι (T.obj n)))
    (hK : ∀ n, D.quotientPullback (D.testHom ι (T.map (homOfLE (n.le_add_right 1))))
      (K (n + 1)).1 = (K n).1) :
    ∃ (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1
        (D.space (D.testOver ι c.pt)).2) (hq : G.IsQuasicoherentOnSite)
      (hfp : G.IsFinitePresentationOnSite)
      (hfl : IsFlatOver B S hS (D.space (D.testOver ι c.pt)).2
        (D.projection (D.testOver ι c.pt)).hom G)
      (hps : D.IsProperlySupportedOver (D.testOver ι c.pt) G)
      (ψ : ∀ n, (modulePullback B S hS (D.toCoherentSituation.relativeMap (D.legHom ι c n))).obj G ≅
        D.quotientModule _ (K n).1),
      ∀ n, (D.towerCoherentStep ι K hK n).comp
          (⟨D.legHom ι c (n + 1), (ψ (n + 1)).hom, Iso.isIso_hom _⟩ :
            CoherentHom (D.cohObject _ (K (n + 1)).1 (K (n + 1)).2)
              (D.toCoherentSituation.objectOf _ G hq hfp hfl
              ⟨D.isLocallyOfFiniteType_projection _, hps.1, hps.2⟩)) =
        ⟨D.legHom ι c n, (ψ n).hom, Iso.isIso_hom _⟩ := by
  let D' := D.toCoherentSituation
  let : Category.{u + 1} (CoherentObject D') := D'.categoryData.category
  have hTE : D'.TowerExistence :=
    D'.towerExistence_of_existence InverseSystemExistenceSituation.exists_flat_algebraization hsep
  let ξ : ℕ ⥤ CoherentObject D' := Functor.ofSequence (X := fun n => D.cohObject _ (K n).1 (K n).2)
    (fun n => D.towerCoherentStep ι K hK n)
  have hξ : ∀ n, (ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _) =
      D.towerCoherentStep ι K hK n := fun n => Functor.ofSequence_map_homOfLE_succ _ n
  let b : ∀ n, (ξ.obj n).T ⟶ D.testOver ι c.pt := fun n => D.legHom ι c n
  have hb : ∀ n, (ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).base ≫ b (n + 1) =
      b n := fun n => by
    rw [hξ]
    show D.testHom ι _ ≫ D.testHom ι _ = D.testHom ι _
    rw [← testHom_comp, c.w]
  obtain ⟨G, hq, hfp, hfl, hps, ψ, hψ⟩ := hTE Λ R cR hcR hsurj hsq (D.testOver ι c.pt) eLimit ξ b
    hb e (fun n => by rw [hξ]; exact he _) heL
  obtain ⟨hp, hcl, hpr⟩ := hps
  refine ⟨G, hq, hfp, hfl, ⟨hcl, hpr⟩, ψ, fun n => ?_⟩
  have := hψ n
  rwa [hξ] at this

section Fullness

variable {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ} {cR : Cone R}
  (hcR : IsLimit cR) {T : ℕ ⥤ BigFppfOver B S hS} (c : Cocone T)
  {e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (T.obj n) ≅ Spec (.of (R.obj (.op n)))}
  {eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt)}
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map (T.map f) ≫ (e j).hom =
      (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (heL : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

variable {c} in
/-- The tower of test schemes over the vertex of a cocone, as a functor. -/
def legFunctor : ℕ ⥤ SchemesOver (schemeSpace c.pt) where
  obj n := legOver c n
  map f := legOverMap c f
  map_id n := CostructuredArrow.hom_ext _ _ (T.map_id n)
  map_comp f g := CostructuredArrow.hom_ext _ _ (T.map_comp f g)

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- A family of elements of a presheaf along a tower, compatible with the successor
transitions, is compatible with all transitions. -/
theorem map_eq_of_succ {C : Type*} [Category C] (F : ℕ ⥤ C) {P : Cᵒᵖ ⥤ Type*}
    (x : ∀ n, P.obj (op (F.obj n)))
    (hx : ∀ n, P.map (F.map (homOfLE (n.le_add_right 1))).op (x (n + 1)) = x n)
    {i j : ℕ} (f : i ⟶ j) : P.map (F.map f).op (x j) = x i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  induction k with
  | zero =>
    obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
    simp
  | succ k ih =>
    obtain rfl : f = homOfLE (i.le_add_right k) ≫ homOfLE ((i + k).le_add_right 1) :=
      Subsingleton.elim _ _
    rw [F.map_comp, op_comp, P.map_comp, types_comp_apply]
    exact (congrArg _ (hx (i + k))).trans (ih _)

/-- The square presenting a base change along a test scheme. -/
theorem isPullback_baseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (W : SchemesOver Y) :
    IsPullback (baseChangeProjection f W) (baseChangeInclusion f W) f W.hom :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS f W.hom

/-- The projection of the base change to the vertex onto the vertex, as a morphism to the
algebraic space of the vertex. -/
def vertexProjection : D.space (D.testOver ι c.pt) ⟶ schemeSpace c.pt :=
  D.projection (D.testOver ι c.pt)

/-- The comparison of a member of the tower of base changes with the base change of the base
change to the vertex. -/
def towerToBaseChange (n : ℕ) : D.space (D.testOver ι (T.obj n)) ⟶
    baseChangeSpace (D.vertexProjection ι c) (legOver c n) :=
  (isPullback_baseChange (D.vertexProjection ι c) (legOver c n)).lift
    (D.relativeMap (D.legHom ι c n)) (D.projection (D.testOver ι (T.obj n)))
    (baseChangeMap_comp_inclusion D.f (D.legHom ι c n))

/-- The inverse comparison. -/
def baseChangeToTower (n : ℕ) : baseChangeSpace (D.vertexProjection ι c) (legOver c n) ⟶
    D.space (D.testOver ι (T.obj n)) :=
  (isPullback_baseChangeMap D.f (D.legHom ι c n)).lift
    (baseChangeProjection (D.vertexProjection ι c) (legOver c n))
    (baseChangeInclusion (D.vertexProjection ι c) (legOver c n))
    (isPullback_baseChange (D.vertexProjection ι c) (legOver c n)).w

/-- The comparison `towerToBaseChange` followed by the projection of the base change is the
morphism of base changes along the leg. -/
@[reassoc (attr := simp)]
theorem towerToBaseChange_projection (n : ℕ) :
    D.towerToBaseChange ι c n ≫ baseChangeProjection (D.vertexProjection ι c) (legOver c n) =
      D.relativeMap (D.legHom ι c n) :=
  IsPullback.lift_fst _ _ _ _

/-- The comparison `towerToBaseChange` followed by the inclusion of the base change is the
projection of the member of the tower. -/
@[reassoc (attr := simp)]
theorem towerToBaseChange_inclusion (n : ℕ) :
    D.towerToBaseChange ι c n ≫ baseChangeInclusion (D.vertexProjection ι c) (legOver c n) =
      D.projection (D.testOver ι (T.obj n)) :=
  IsPullback.lift_snd _ _ _ _

/-- The inverse comparison `baseChangeToTower` followed by the morphism of base changes along the
leg is the projection of the base change. -/
@[reassoc (attr := simp)]
theorem baseChangeToTower_relativeMap (n : ℕ) :
    D.baseChangeToTower ι c n ≫ D.relativeMap (D.legHom ι c n) =
      baseChangeProjection (D.vertexProjection ι c) (legOver c n) :=
  IsPullback.lift_fst _ _ _ _

/-- The inverse comparison `baseChangeToTower` followed by the projection of the member of the
tower is the inclusion of the base change. -/
@[reassoc (attr := simp)]
theorem baseChangeToTower_projection (n : ℕ) :
    D.baseChangeToTower ι c n ≫ D.projection (D.testOver ι (T.obj n)) =
      baseChangeInclusion (D.vertexProjection ι c) (legOver c n) :=
  IsPullback.lift_snd _ _ _ _

/-- The comparison `towerToBaseChange` followed by its inverse `baseChangeToTower` is the
identity. -/
theorem towerToBaseChange_baseChangeToTower (n : ℕ) :
    D.towerToBaseChange ι c n ≫ D.baseChangeToTower ι c n = 𝟙 _ :=
  (isPullback_baseChangeMap D.f (D.legHom ι c n)).hom_ext (by simp) (by simp)

/-- The morphism of base changes along a transition of the tower, followed by the one along the
next leg, is the morphism of base changes along the previous leg. -/
theorem towerOverMap_w (n : ℕ) :
    D.relativeMap (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))) ≫
        D.relativeMap (D.legHom ι c (n + 1)) =
      D.relativeMap (D.legHom ι c n) := by
  show baseChangeMap D.f _ ≫ baseChangeMap D.f (D.testHom ι _) =
    baseChangeMap D.f (D.testHom ι _)
  rw [← baseChangeMap_comp, ← testHom_comp, c.w]

/-- The inverse comparisons `baseChangeToTower` commute with the transitions: of the base changes
of the tower of test schemes over the vertex, and of the tower of base changes. -/
theorem baseChangeMap_baseChangeToTower (n : ℕ) :
    baseChangeMap (D.vertexProjection ι c) (legOverMap c (homOfLE (n.le_add_right 1))) ≫
        D.baseChangeToTower ι c (n + 1) =
      D.baseChangeToTower ι c n ≫
        D.relativeMap (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))) := by
  refine (isPullback_baseChangeMap D.f (D.legHom ι c (n + 1))).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, baseChangeToTower_relativeMap, D.towerOverMap_w ι c n,
      baseChangeToTower_relativeMap, baseChangeMap_comp_projection]
  · rw [Category.assoc, Category.assoc, baseChangeToTower_projection]
    show _ = _ ≫ baseChangeMap D.f _ ≫ baseChangeInclusion D.f _
    rw [baseChangeMap_comp_inclusion, baseChangeMap_comp_inclusion D.f,
      ← Category.assoc, baseChangeToTower_projection]
    rfl

/-- The comparison of the base change to the vertex with its base change along the identity. -/
def vertexToBaseChange : D.space (D.testOver ι c.pt) ⟶
    baseChangeSpace (D.vertexProjection ι c) (vertexOver c) :=
  (isPullback_baseChange (D.vertexProjection ι c) (vertexOver c)).lift
    (𝟙 _) (D.vertexProjection ι c)
    (by rw [Category.id_comp]; exact (Category.comp_id _).symm)

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- The comparison `vertexToBaseChange` followed by the projection of the base change along the
identity is the identity. -/
@[reassoc (attr := simp)]
theorem vertexToBaseChange_projection :
    D.vertexToBaseChange ι c ≫ baseChangeProjection (D.vertexProjection ι c) (vertexOver c) =
      𝟙 _ :=
  IsPullback.lift_fst _ _ _ _

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- The comparison `vertexToBaseChange` followed by the inclusion of the base change along the
identity is the projection of the base change to the vertex. -/
@[reassoc (attr := simp)]
theorem vertexToBaseChange_inclusion :
    D.vertexToBaseChange ι c ≫ baseChangeInclusion (D.vertexProjection ι c) (vertexOver c) =
      D.vertexProjection ι c :=
  IsPullback.lift_snd _ _ _ _

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- The projection of the base change along the identity followed by the comparison
`vertexToBaseChange` is the identity. -/
theorem baseChangeProjection_vertexToBaseChange :
    baseChangeProjection (D.vertexProjection ι c) (vertexOver c) ≫ D.vertexToBaseChange ι c =
      𝟙 _ :=
  (isPullback_baseChange (D.vertexProjection ι c) (vertexOver c)).hom_ext
    (by simp) (by
      simp only [Category.assoc, vertexToBaseChange_inclusion, Category.id_comp]
      exact (isPullback_baseChange (D.vertexProjection ι c) (vertexOver c)).w.trans
        (Category.comp_id _))

/-- The base change of the base change to the vertex along the identity is the base change to
the vertex. -/
def vertexBaseChangeIso : baseChangeSpace (D.vertexProjection ι c) (vertexOver c) ≅
    D.space (D.testOver ι c.pt) where
  hom := baseChangeProjection (D.vertexProjection ι c) (vertexOver c)
  inv := D.vertexToBaseChange ι c
  hom_inv_id := D.baseChangeProjection_vertexToBaseChange ι c
  inv_hom_id := D.vertexToBaseChange_projection ι c

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- Conjugating the inverse image of a morphism along `g` by the comparison for `f ≫ g = k` gives
its inverse image along `k`. -/
theorem conjHom_modulePullbackTriangle_map {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (α : M ⟶ N) :
    Functor.conjHom (modulePullbackTriangle B S hS hk) ((modulePullback B S hS g).map α) =
      (modulePullback B S hS k).map α := by
  simp only [Functor.conjHom]
  rw [← Functor.comp_map, ← (modulePullbackTriangle B S hS hk).hom.naturality_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- Conjugating twice is conjugating along the composite. -/
theorem conjHom_modulePullbackTriangle_comp {V W X Z : AlgebraicSpaces B S hS} {f : V ⟶ W}
    {g : W ⟶ X} {p : X ⟶ Z} {q : W ⟶ Z} {r : V ⟶ Z} (h₁ : f ≫ q = r) (h₂ : g ≫ p = q)
    (h₁₂ : (f ≫ g) ≫ p = r) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    Functor.conjHom (modulePullbackTriangle B S hS h₁)
        (Functor.conjHom (modulePullbackTriangle B S hS h₂) α) =
      Functor.conjHom (modulePullbackTriangle B S hS h₁₂) α :=
  (Functor.conjHom_comp _ _ _ (modulePullbackTriangle B S hS (rfl : f ≫ g = f ≫ g))
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp' rfl h₂ h₁ h₁₂) α).symm

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- The conjugation only depends on the morphism, not on its presentation. -/
theorem conjHom_modulePullbackTriangle_congr {X Y Z : AlgebraicSpaces B S hS} {f f' : X ⟶ Y}
    (hff : f = f') {g : Y ⟶ Z} {k : X ⟶ Z} (h : f ≫ g = k) (h' : f' ≫ g = k)
    {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N) :
    Functor.conjHom (modulePullbackTriangle B S hS h) α =
      Functor.conjHom (modulePullbackTriangle B S hS h') α := by
  subst hff
  rfl

/-- The family of maps out of the tower of base changes of `F_T` attached to a family of maps
out of the tower of base changes of `F`. -/
def towerHomFamily
    (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1 (D.space (D.testOver ι c.pt)).2)
    (φ : ∀ n, D.baseChangeModule (D.testOver ι (T.obj n)) ⟶
      (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).obj G) (n : ℕ) :
    (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).obj
        (D.baseChangeModule (D.testOver ι c.pt)) ⟶
      (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).obj G :=
  Functor.conjInv (D.baseChangeComparison (D.legHom ι c n)) (φ n)

/-- The family `towerHomFamily` is compatible with the transitions of the tower: conjugating its
member at `n + 1` along a transition gives its member at `n`. -/
theorem towerHomFamily_compat
    (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1 (D.space (D.testOver ι c.pt)).2)
    (φ : ∀ n, D.baseChangeModule (D.testOver ι (T.obj n)) ⟶
      (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).obj G)
    (hφ : ∀ n, Functor.conjTransition
        (D.baseChangeComparison (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))))
        (modulePullbackTriangle B S hS (D.towerOverMap_w ι c n)) (φ (n + 1)) = φ n) (n : ℕ) :
    Functor.conjHom (modulePullbackTriangle B S hS (D.towerOverMap_w ι c n))
      (D.towerHomFamily ι c G φ (n + 1)) = D.towerHomFamily ι c G φ n :=
  Functor.conjHom_inv_app_comp_eq
    (modulePullbackTriangle B S hS (D.towerOverMap_w ι c n))
    (D.baseChangeComparison (D.legHom ι c (n + 1)))
    (D.baseChangeComparison (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))))
    (D.baseChangeComparison (D.legHom ι c n))
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp (D.towerOverMap_w ι c n)
      (baseChangeMap_comp_projection D.f (D.legHom ι c (n + 1)))
      (baseChangeMap_comp_projection D.f (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))))
      (baseChangeMap_comp_projection D.f (D.legHom ι c n)))
    (φ (n + 1)) (φ n) (hφ n)

/-- The family of maps over the tower of test schemes over the vertex. -/
def vertexHomFamily
    (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1 (D.space (D.testOver ι c.pt)).2)
    (φ : ∀ n, D.baseChangeModule (D.testOver ι (T.obj n)) ⟶
      (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).obj G) (n : ℕ) :
    (modulePullback B S hS (baseChangeProjection (D.vertexProjection ι c) (legOver c n))).obj
        (D.baseChangeModule (D.testOver ι c.pt)) ⟶
      (modulePullback B S hS (baseChangeProjection (D.vertexProjection ι c) (legOver c n))).obj
        G :=
  Functor.conjHom (modulePullbackTriangle B S hS (D.baseChangeToTower_relativeMap ι c n))
    (D.towerHomFamily ι c G φ n)

/-- The family `vertexHomFamily` is compatible with the transitions of the tower of test schemes
over the vertex: conjugating its member at `n + 1` along a transition gives its member at `n`. -/
theorem vertexHomFamily_compat
    (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1 (D.space (D.testOver ι c.pt)).2)
    (φ : ∀ n, D.baseChangeModule (D.testOver ι (T.obj n)) ⟶
      (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).obj G)
    (hφ : ∀ n, Functor.conjTransition
        (D.baseChangeComparison (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))))
        (modulePullbackTriangle B S hS (D.towerOverMap_w ι c n)) (φ (n + 1)) = φ n) (n : ℕ) :
    Functor.conjHom (modulePullbackTriangle B S hS (baseChangeMap_comp_projection
        (D.vertexProjection ι c) (legOverMap c (homOfLE (n.le_add_right 1)))))
      (D.vertexHomFamily ι c G φ (n + 1)) = D.vertexHomFamily ι c G φ n := by
  have hsq := D.baseChangeMap_baseChangeToTower ι c n
  rw [vertexHomFamily, vertexHomFamily, conjHom_modulePullbackTriangle_comp _ _
      (by rw [Category.assoc, baseChangeToTower_relativeMap, baseChangeMap_comp_projection]),
    conjHom_modulePullbackTriangle_congr hsq _
      (by rw [Category.assoc, D.towerOverMap_w ι c n, baseChangeToTower_relativeMap]),
    ← conjHom_modulePullbackTriangle_comp (D.baseChangeToTower_relativeMap ι c n)
      (D.towerOverMap_w ι c n), D.towerHomFamily_compat ι c G φ hφ n]

/-- The family of maps over the tower of test schemes over the vertex, as elements of the
relative Hom functor. -/
def vertexHomElem
    (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1 (D.space (D.testOver ι c.pt)).2)
    (φ : ∀ n, D.baseChangeModule (D.testOver ι (T.obj n)) ⟶
      (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).obj G) (n : ℕ) :
    ((baseChangeOver (D.vertexProjection ι c)).op ⋙ moduleHomOver
      (modulePushforwardCoherence B S hS) (D.baseChangeModule (D.testOver ι c.pt)) G).obj
        (op ((legFunctor (c := c)).obj n)) :=
  D.vertexHomFamily ι c G φ n

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- The action of the relative Hom functor over the algebraic spaces on a morphism. -/
theorem moduleHomOver_map_apply {X : AlgebraicSpaces B S hS}
    (hc : ModulePushforwardCoherence B S hS) (F G : Modules.{u, u} B S hS X.1 X.2)
    {Z Z' : Over X} (m : Z ⟶ Z') :
    (moduleHomOver hc F G).map m.op =
      TypeCat.ofHom (Functor.conjHom (M := F) (N := G)
        (modulePullbackTriangle B S hS (Over.w m))) :=
  rfl

omit [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)] in
/-- The action of the relative Hom functor along a test scheme on a morphism of test schemes,
as conjugation by the comparison of the two base changes. -/
theorem baseChangeOver_moduleHomOver_map_apply {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M N : Modules.{u, u} B S hS X.1 X.2) {U W : SchemesOver Y} (g : U ⟶ W)
    (α : ((baseChangeOver f).op ⋙ moduleHomOver (modulePushforwardCoherence B S hS) M N).obj
      (op W)) :
    ((baseChangeOver f).op ⋙ moduleHomOver (modulePushforwardCoherence B S hS) M N).map g.op α =
      Functor.conjHom (M := M) (N := N)
        (modulePullbackTriangle B S hS (baseChangeMap_comp_projection f g)) α := by
  rw [Functor.comp_map, Functor.op_map, moduleHomOver_map_apply]
  exact TypeCat.ofHom_apply _ α

include hcR he heL in
/-- **Maps out of the tower of base changes of `F` into the restrictions of a module with proper
support, flat over the vertex, come from a map on the base change to the vertex** (the fullness
half of Grothendieck's existence theorem along a tower, from Stacks 08K6). No square-zero
hypothesis is used. -/
theorem exists_hom_of_tower (hF : D.F.IsFinitePresentationOnSite)
    (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1 (D.space (D.testOver ι c.pt)).2)
    (hq : G.IsQuasicoherentOnSite) (hfp : G.IsFinitePresentationOnSite)
    (hfl : IsFlatOver B S hS (D.space (D.testOver ι c.pt)).2
      (D.projection (D.testOver ι c.pt)).hom G)
    (hps : D.IsProperlySupportedOver (D.testOver ι c.pt) G)
    (φ : ∀ n, D.baseChangeModule (D.testOver ι (T.obj n)) ⟶
      (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).obj G)
    (hφ : ∀ n, Functor.conjTransition
        (D.baseChangeComparison (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))))
        (modulePullbackTriangle B S hS (D.towerOverMap_w ι c n)) (φ (n + 1)) = φ n) :
    ∃ u : D.baseChangeModule (D.testOver ι c.pt) ⟶ G,
      ∀ n, (modulePullback B S hS (D.relativeMap (D.legHom ι c n))).map u =
        Functor.conjInv (D.baseChangeComparison (D.legHom ι c n)) (φ n) := by
  have hqF : (D.baseChangeModule (D.testOver ι c.pt)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ D.F D.quasicoherent
  have hfpF : (D.baseChangeModule (D.testOver ι c.pt)).IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePullback B S hS _ D.F hF
  have hRf : IsAffineAlgebraicSpaceOver (schemeSpace c.pt)
      ((baseChangeOver (D.vertexProjection ι c)).op ⋙ moduleHomOver
        (modulePushforwardCoherence B S hS) (D.baseChangeModule (D.testOver ι c.pt)) G) :=
    (HomSituation.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation
      ⟨D.space (D.testOver ι c.pt), schemeSpace c.pt, D.vertexProjection ι c,
        D.baseChangeModule (D.testOver ι c.pt), G, hqF, hq⟩
      (D.toCoherentSituation.isFinitePresentation_projection _) hfpF hfp hfl
      hps).isAffineAlgebraicSpaceOver
  have hx : ∀ n, ((baseChangeOver (D.vertexProjection ι c)).op ⋙ moduleHomOver
      (modulePushforwardCoherence B S hS) (D.baseChangeModule (D.testOver ι c.pt)) G).map
        ((legFunctor (c := c)).map (homOfLE (n.le_add_right 1))).op
        (D.vertexHomElem ι c G φ (n + 1)) = D.vertexHomElem ι c G φ n := fun n => by
    rw [baseChangeOver_moduleHomOver_map_apply]
    exact D.vertexHomFamily_compat ι c G φ hφ n
  obtain ⟨v, hv⟩ := exists_eq_of_isAffineAlgebraicSpaceOver_cocone hcR he heL hRf
    (D.vertexHomElem ι c G φ)
    (fun f => map_eq_of_succ (legFunctor (c := c)) (D.vertexHomElem ι c G φ) hx f)
  set E := (modulePushforwardCoherence B S hS).modulePullbackHomEquiv (D.vertexBaseChangeIso ι c)
    (D.baseChangeModule (D.testOver ι c.pt)) G
  refine ⟨E.symm v, fun n => ?_⟩
  have hvu : (modulePullback B S hS
      (baseChangeProjection (D.vertexProjection ι c) (vertexOver c))).map (E.symm v) = v :=
    E.apply_symm_apply v
  have h := hv n
  rw [baseChangeOver_moduleHomOver_map_apply, ← hvu, conjHom_modulePullbackTriangle_map] at h
  have h3 := congrArg (Functor.conjHom
    (modulePullbackTriangle B S hS (D.towerToBaseChange_projection ι c n)))
    (show (modulePullback B S hS
      (baseChangeProjection (D.vertexProjection ι c) (legOver c n))).map (E.symm v) =
        D.vertexHomFamily ι c G φ n from h)
  rw [conjHom_modulePullbackTriangle_map, vertexHomFamily,
    conjHom_modulePullbackTriangle_comp _ _
      (by rw [Category.assoc, baseChangeToTower_relativeMap, towerToBaseChange_projection]),
    conjHom_modulePullbackTriangle_congr (D.towerToBaseChange_baseChangeToTower ι c n) _
      (Category.id_comp _), Functor.conjHom_id _ _
        ((modulePushforwardCoherence B S hS).modulePullbackTriangle_id (Category.id_comp _))] at h3
  exact h3

/-- The first member of the tower of base changes maps onto the base change to the vertex, when
the first member of the tower of test schemes maps onto the vertex. -/
theorem surjective_pointsMap_relativeMap_legHom
    (hsurj0 : Function.Surjective ⇑((BigFppfOver.toScheme B S hS).map (c.ι.app 0))) :
    Function.Surjective (pointsMap B S hS (D.space (D.testOver ι (T.obj 0))).1
      (D.relativeMap (D.legHom ι c 0)).hom) := by
  intro x
  obtain ⟨y, hy⟩ := (surjective_pointsMap_yoneda_iff B S hS (c.ι.app 0)).2 hsurj0
    (pointsMap B S hS _ (D.projection (D.testOver ι c.pt)).hom x)
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f (D.legHom ι c 0)))
    x y hy.symm
  exact ⟨w, hw⟩

include hcR he heL in
/-- **The core of the effectiveness of towers of quotients.** Given an algebraization `G` of the
quotients `Q_n` of a tower (isomorphisms `ψ n` compatible with the transitions, as produced by
Grothendieck's existence theorem), and assuming that surjectivity of a morphism onto `G` can be
checked on the first member of the tower, the tower of quotients comes from a quotient over the
vertex. No square-zero hypothesis is used. -/
theorem exists_quotient_of_tower_of_algebraization_of_epi (hF : D.F.IsFinitePresentationOnSite)
    (K : ∀ n, D.properlySupportedQuotients (D.testOver ι (T.obj n)))
    (hK : ∀ n, D.quotientPullback (D.testHom ι (T.map (homOfLE (n.le_add_right 1))))
      (K (n + 1)).1 = (K n).1)
    (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1 (D.space (D.testOver ι c.pt)).2)
    (hq : G.IsQuasicoherentOnSite) (hfp : G.IsFinitePresentationOnSite)
    (hfl : IsFlatOver B S hS (D.space (D.testOver ι c.pt)).2
      (D.projection (D.testOver ι c.pt)).hom G)
    (hps : D.IsProperlySupportedOver (D.testOver ι c.pt) G)
    (hepi0 : ∀ u : D.baseChangeModule (D.testOver ι c.pt) ⟶ G,
      Epi ((modulePullback B S hS (D.relativeMap (D.legHom ι c 0))).map u) → Epi u)
    (ψ : ∀ n, (modulePullback B S hS (D.toCoherentSituation.relativeMap (D.legHom ι c n))).obj G ≅
      D.quotientModule _ (K n).1)
    (hψ : ∀ n, (D.towerCoherentStep ι K hK n).comp
        (⟨D.legHom ι c (n + 1), (ψ (n + 1)).hom, Iso.isIso_hom _⟩ :
          CoherentHom (D.cohObject _ (K (n + 1)).1 (K (n + 1)).2)
            (D.toCoherentSituation.objectOf _ G hq hfp hfl
              ⟨D.isLocallyOfFiniteType_projection _, hps.1, hps.2⟩)) =
        ⟨D.legHom ι c n, (ψ n).hom, Iso.isIso_hom _⟩) :
    ∃ K' : D.properlySupportedQuotients (D.testOver ι c.pt),
      ∀ n, D.quotientPullback (D.legHom ι c n) K'.1 = (K n).1 := by
  have hφ : ∀ n, Functor.conjTransition
      (D.baseChangeComparison (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))))
      (modulePullbackTriangle B S hS (D.towerOverMap_w ι c n))
      (D.quotientProjection _ (K (n + 1)).1 ≫ (ψ (n + 1)).inv) =
        D.quotientProjection _ (K n).1 ≫ (ψ n).inv := fun n => by
    have hw : D.toCoherentSituation.relativeMap
        (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))) ≫
        D.toCoherentSituation.relativeMap (D.legHom ι c (n + 1)) =
          D.toCoherentSituation.relativeMap (D.legHom ι c n) := D.towerOverMap_w ι c n
    have hB := CoherentSituation.fibre_eq_of_comp_eq D.toCoherentSituation
      (A₀ := D.cohObject _ (K n).1 (K n).2) (A₁ := D.cohObject _ (K (n + 1)).1 (K (n + 1)).2)
      (A := D.toCoherentSituation.objectOf _ G hq hfp hfl
        ⟨D.isLocallyOfFiniteType_projection _, hps.1, hps.2⟩)
      (D.towerCoherentStep ι K hK n) (b₁ := D.legHom ι c (n + 1)) (b₀ := D.legHom ι c n)
      (ψ (n + 1)) (ψ n) (hψ n) hw
    have hA := Functor.conjTransition_comp_inv_eq
      (D.toCoherentSituation.presentationComparison
        (D.testHom ι (T.map (homOfLE (n.le_add_right 1)))))
      (modulePullbackTriangle B S hS hw)
      (D.presentation _ (K (n + 1)).1) (D.presentation _ (K n).1)
      (D.cohFibreOfEq _ (hK n)) (D.towerCoherentStep_isPinned ι K hK n) (ψ (n + 1))
      (ψ n) hB
    exact hA
  obtain ⟨u, hu⟩ := D.exists_hom_of_tower ι hcR c he heL hF G hq hfp hfl hps
    (fun n => D.quotientProjection _ (K n).1 ≫ (ψ n).inv) hφ
  have hepi : Epi u := by
    refine hepi0 u ?_
    rw [hu 0]
    simp only [Functor.conjInv]
    have e1 : Epi ((D.baseChangeComparison (D.legHom ι c 0)).inv.app D.F) :=
      @IsIso.epi_of_iso _ _ _ _ _
        (Iso.isIso_inv ((D.baseChangeComparison (D.legHom ι c 0)).app D.F))
    have e2 : Epi (D.quotientProjection _ (K 0).1) :=
      QuotientSituation.epi_quotientProjection _ _ _
    have e3 : Epi (ψ 0).inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv (ψ 0))
    exact @epi_comp _ _ _ _ _ _ e1 _ (@epi_comp _ _ _ _ _ _ e2 _ e3)
  let e := Abelian.cokernelKernelSubobjectIso u
  refine ⟨⟨kernelSubobject u, ⟨⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm hq,
      IsFlatOver.of_iso B S hS _ e.symm hfl⟩,
      SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm hfp⟩,
    D.isProperlySupportedOver_of_iso e.symm hps⟩, fun n => ?_⟩
  exact Functor.conjSubobject_kernelSubobject (D.baseChangeComparison (D.legHom ι c n)) u
    (K n).1 (ψ n) (hu n)

include hcR he heL in
/-- **The core of the effectiveness of towers of quotients.** Given an algebraization `G` of the
quotients `Q_n` of a tower (isomorphisms `ψ n` compatible with the transitions, as produced by
Grothendieck's existence theorem), and assuming the first member of the tower of test schemes
maps onto the vertex, the tower of quotients comes from a quotient over the vertex. No
square-zero hypothesis is used. -/
theorem exists_quotient_of_tower_of_algebraization (hF : D.F.IsFinitePresentationOnSite)
    (hsurj0 : Function.Surjective ⇑((BigFppfOver.toScheme B S hS).map (c.ι.app 0)))
    (K : ∀ n, D.properlySupportedQuotients (D.testOver ι (T.obj n)))
    (hK : ∀ n, D.quotientPullback (D.testHom ι (T.map (homOfLE (n.le_add_right 1))))
      (K (n + 1)).1 = (K n).1)
    (G : Modules.{u, u} B S hS (D.space (D.testOver ι c.pt)).1 (D.space (D.testOver ι c.pt)).2)
    (hq : G.IsQuasicoherentOnSite) (hfp : G.IsFinitePresentationOnSite)
    (hfl : IsFlatOver B S hS (D.space (D.testOver ι c.pt)).2
      (D.projection (D.testOver ι c.pt)).hom G)
    (hps : D.IsProperlySupportedOver (D.testOver ι c.pt) G)
    (ψ : ∀ n, (modulePullback B S hS (D.toCoherentSituation.relativeMap (D.legHom ι c n))).obj G ≅
      D.quotientModule _ (K n).1)
    (hψ : ∀ n, (D.towerCoherentStep ι K hK n).comp
        (⟨D.legHom ι c (n + 1), (ψ (n + 1)).hom, Iso.isIso_hom _⟩ :
          CoherentHom (D.cohObject _ (K (n + 1)).1 (K (n + 1)).2)
            (D.toCoherentSituation.objectOf _ G hq hfp hfl
              ⟨D.isLocallyOfFiniteType_projection _, hps.1, hps.2⟩)) =
        ⟨D.legHom ι c n, (ψ n).hom, Iso.isIso_hom _⟩) :
    ∃ K' : D.properlySupportedQuotients (D.testOver ι c.pt),
      ∀ n, D.quotientPullback (D.legHom ι c n) K'.1 = (K n).1 := by
  have hqF : (D.baseChangeModule (D.testOver ι c.pt)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ D.F D.quasicoherent
  have := hfp
  have hGft : SheafOfModules.IsFiniteTypeOnSite G := inferInstance
  exact D.exists_quotient_of_tower_of_algebraization_of_epi ι hcR c he heL hF K hK G hq hfp hfl hps
    (fun u hu => epi_of_epi_modulePullback_of_surjective (D.relativeMap (D.legHom ι c 0))
      (D.surjective_pointsMap_relativeMap_legHom ι c hsurj0) hqF hq hGft u hu) ψ hψ

include hcR heL in
/-- **The first member of a square-zero tower of spectra maps onto the vertex**: the kernel of
`lim Rₙ ⟶ R₀` is nil, since every transition has square-zero kernel. -/
theorem surjective_toScheme_map_ι_zero
    (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
    (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), (RingHom.ker (R.map f).hom.toRingHom) ^ 2 = ⊥) :
    Function.Surjective ⇑((BigFppfOver.toScheme B S hS).map (c.ι.app 0)) := by
  have hA := CommAlgCat.isLimitForget₂CommRingCat hcR
  let π₀ : CommRingCat.of cR.pt ⟶ CommRingCat.of (R.obj (op 0)) :=
    CommRingCat.ofHom (cR.π.app (op 0)).hom.toRingHom
  have hπs : Function.Surjective π₀.hom :=
    Concrete.surjective_π_app_zero_of_surjective_map hA (fun n => hsurj _)
  have hk : RingHom.ker π₀.hom ≤ nilradical (CommRingCat.of cR.pt) := by
    intro x hx
    refine ⟨2, (Ideal.mem_bot).2 (Concrete.isLimit_ext _ hA (x ^ 2) 0 fun j => ?_)⟩
    obtain ⟨n⟩ := j
    have hw := congrArg (fun g => g.hom x) (cR.w (homOfLE (Nat.zero_le n)).op)
    have hxn : (cR.π.app (op n)).hom x ∈
        RingHom.ker (R.map (homOfLE (Nat.zero_le n)).op).hom.toRingHom := by
      rw [RingHom.mem_ker]
      exact hw.trans hx
    have h2 : ((cR.π.app (op n)).hom x) ^ 2 ∈
        RingHom.ker (R.map (homOfLE (Nat.zero_le n)).op).hom.toRingHom ^ 2 :=
      Ideal.pow_mem_pow hxn 2
    rw [hsq, Ideal.mem_bot] at h2
    show (cR.π.app (op n)).hom (x ^ 2) = (cR.π.app (op n)).hom 0
    rw [map_pow, map_zero, h2]
  intro y
  obtain ⟨p, hp⟩ := Spec_map_base_surjective_of_ker_le_nilradical π₀ hπs hk (eLimit.hom y)
  refine ⟨(e 0).inv p, (Scheme.homeoOfIso eLimit).injective ?_⟩
  show eLimit.hom ((BigFppfOver.toScheme B S hS).map (c.ι.app 0) ((e 0).inv p)) =
    eLimit.hom y
  rw [← Scheme.Hom.comp_apply, heL 0, Scheme.Hom.comp_apply,
    show (e 0).hom ((e 0).inv p) = p from (Scheme.homeoOfIso (e 0)).apply_symm_apply p]
  exact hp

end Fullness

end QuotSituation

end AlgebraicGeometry.Space

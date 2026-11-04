module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardKernelDescentData
public import StacksFrontier.AlgebraicGeometry.Quot.PicardInvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcDescentTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FamilyPullback
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom

/-!
# Descending a locally trivialized invertible module to the test scheme

The descent datum of a local trivialization of an invertible module on the covering family
`{U i ⟶ T}` is effective by fpqc descent of quasi-coherent modules on
algebraic spaces (Stacks 04W8), giving a quasi-coherent module `N` on `T` with isomorphisms
`α i : 𝒪_{U i} ≅ N|_{U i}` compatible with the transitions.  This file shows that `N` is invertible
and that its inverse image to `X_T` is `L`: on `X_{U i}` the two are identified through `α i` and
the trivialization of `L`, these identifications are compatible with the canonical descent data
on the overlaps, and the canonical descent functor of the fpqc covering `{X_{U i} ⟶ X_T}` is
fully faithful.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_squares`: a coherence of the
  canonical comparisons of inverse images along two commutative squares.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumIsoMk`: compatible
  isomorphisms of inverse images give an isomorphism of canonical descent data.
* `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.α_reading`: the components of the
  descent isomorphism intertwine the transitions with the canonical comparisons on every test
  space.
* `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.isInvertibleModule_descended` and
  `AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.nonempty_iso_descended`: **the
  descended module is invertible and pulls back to `L`.**

## References

* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open QuasiCoherentDescent

/-- The canonical comparison along a first morphism equal to another one. -/
theorem _root_.AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_congr_left
    {A P Q R : AlgebraicSpaces B S hS} {x x' : P ⟶ Q} (hx : x = x') (y : P ⟶ R) (fi : Q ⟶ A)
    (fj : R ⟶ A) (h : x ≫ fi = y ≫ fj) (h' : x' ≫ fi = y ≫ fj)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison x y fi fj h M =
      eqToIso (congrArg (fun r : P ⟶ Q ↦ (modulePullback B S hS r).obj
        ((modulePullback B S hS fi).obj M)) hx) ≪≫ canonicalComparison x' y fi fj h' M := by
  subst hx
  simp

/-- **Canonical comparisons of a module along two commutative squares.**  For two squares
`f₁ ≫ g = h₁ ≫ e₁` and `f₂ ≫ g = h₂ ≫ e₂` and two morphisms `p₁, p₂` out of one space with
`p₁ ≫ f₁ = p₂ ≫ f₂`, the two ways of comparing `p₁^*f₁^*g^*M` with `p₂^*h₂^*e₂^*M` through
canonical comparisons agree. -/
theorem _root_.AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_squares
    {A X P Q₁ Q₂ R₁ R₂ : AlgebraicSpaces B S hS} (p₁ : P ⟶ Q₁) (p₂ : P ⟶ Q₂) (f₁ : Q₁ ⟶ X)
    (f₂ : Q₂ ⟶ X) (g : X ⟶ A) (h₁ : Q₁ ⟶ R₁) (h₂ : Q₂ ⟶ R₂) (e₁ : R₁ ⟶ A) (e₂ : R₂ ⟶ A)
    (sq₁ : f₁ ≫ g = h₁ ≫ e₁) (sq₂ : f₂ ≫ g = h₂ ≫ e₂) (hp : p₁ ≫ f₁ = p₂ ≫ f₂)
    (hc : (p₁ ≫ h₁) ≫ e₁ = (p₂ ≫ h₂) ≫ e₂) (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS p₁).mapIso (canonicalComparison f₁ h₁ g e₁ sq₁ M) ≪≫
        (pullbackComparison B S hS p₁ h₁ (p₁ ≫ h₁) rfl ((modulePullback B S hS e₁).obj M)).symm ≪≫
        canonicalComparison (p₁ ≫ h₁) (p₂ ≫ h₂) e₁ e₂ hc M ≪≫
        pullbackComparison B S hS p₂ h₂ (p₂ ≫ h₂) rfl ((modulePullback B S hS e₂).obj M) =
      canonicalComparison p₁ p₂ f₁ f₂ hp ((modulePullback B S hS g).obj M) ≪≫
        (modulePullback B S hS p₂).mapIso (canonicalComparison f₂ h₂ g e₂ sq₂ M) := by
  have h₁' : (p₁ ≫ f₁) ≫ g = (p₁ ≫ h₁) ≫ e₁ := by
    rw [Category.assoc, sq₁, Category.assoc]
  have h₂' : (p₂ ≫ f₂) ≫ g = (p₂ ≫ h₂) ≫ e₂ := by
    rw [Category.assoc, sq₂, Category.assoc]
  rw [modulePullback_mapIso_canonicalComparison B S hS p₁ f₁ h₁ g e₁ sq₁ (p₁ ≫ f₁) (p₁ ≫ h₁)
      rfl rfl h₁' M,
    modulePullback_mapIso_canonicalComparison B S hS p₂ f₂ h₂ g e₂ sq₂ (p₂ ≫ f₂) (p₂ ≫ h₂)
      rfl rfl h₂' M]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [← Iso.trans_assoc (canonicalComparison (p₁ ≫ f₁) (p₁ ≫ h₁) g e₁ h₁' M),
    canonicalComparison_trans, canonicalComparison_congr_left hp (p₂ ≫ h₂) g e₂ _ (by
      rw [h₂']),
    canonicalComparison]
  simp only [Iso.trans_assoc]
  rw [canonicalComparison]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

/-- `canonicalComparison_squares`, solved for the composite before the last comparison. -/
theorem _root_.AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_squares_assoc
    {A X P Q₁ Q₂ R₁ R₂ : AlgebraicSpaces B S hS} (p₁ : P ⟶ Q₁) (p₂ : P ⟶ Q₂) (f₁ : Q₁ ⟶ X)
    (f₂ : Q₂ ⟶ X) (g : X ⟶ A) (h₁ : Q₁ ⟶ R₁) (h₂ : Q₂ ⟶ R₂) (e₁ : R₁ ⟶ A) (e₂ : R₂ ⟶ A)
    (sq₁ : f₁ ≫ g = h₁ ≫ e₁) (sq₂ : f₂ ≫ g = h₂ ≫ e₂) (hp : p₁ ≫ f₁ = p₂ ≫ f₂)
    (hc : (p₁ ≫ h₁) ≫ e₁ = (p₂ ≫ h₂) ≫ e₂) (M : Modules.{u, u} B S hS A.1 A.2)
    {K : Modules.{u, u} B S hS P.1 P.2}
    (k : (modulePullback B S hS (p₂ ≫ h₂)).obj ((modulePullback B S hS e₂).obj M) ≅ K) :
    (modulePullback B S hS p₁).mapIso (canonicalComparison f₁ h₁ g e₁ sq₁ M) ≪≫
        (pullbackComparison B S hS p₁ h₁ (p₁ ≫ h₁) rfl ((modulePullback B S hS e₁).obj M)).symm ≪≫
        canonicalComparison (p₁ ≫ h₁) (p₂ ≫ h₂) e₁ e₂ hc M ≪≫ k =
      canonicalComparison p₁ p₂ f₁ f₂ hp ((modulePullback B S hS g).obj M) ≪≫
        (modulePullback B S hS p₂).mapIso (canonicalComparison f₂ h₂ g e₂ sq₂ M) ≪≫
        (pullbackComparison B S hS p₂ h₂ (p₂ ≫ h₂) rfl ((modulePullback B S hS e₂).obj M)).symm ≪≫
        k := by
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc] using
    congrArg (fun x ↦ x ≪≫ (pullbackComparison B S hS p₂ h₂ (p₂ ≫ h₂) rfl
      ((modulePullback B S hS e₂).obj M)).symm ≪≫ k)
      (canonicalComparison_squares p₁ p₂ f₁ f₂ g h₁ h₂ e₁ e₂ sq₁ sq₂ hp hc M)

/-- A family of isomorphisms of the inverse images of two quasi-coherent modules, compatible with
the canonical comparisons on the pairwise fibre products, is an isomorphism of their canonical
descent data. -/
def _root_.AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatumIsoMk
    {I : Type*} {X : AlgebraicSpaces B S hS} {Y : I → AlgebraicSpaces B S hS} {f : ∀ i, Y i ⟶ X}
    {P Q : Modules.{u, u} B S hS X.1 X.2} (hP : P.IsQuasicoherentOnSite)
    (hQ : Q.IsQuasicoherentOnSite)
    (κ : ∀ i, (modulePullback B S hS (f i)).obj P ≅ (modulePullback B S hS (f i)).obj Q)
    (hκ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).map (κ i).hom ≫
        (canonicalComparison (pairFst B S hS Y f i j) (pairSnd B S hS Y f i j) (f i) (f j)
          (pair_condition B S hS Y f i j) Q).hom =
      (canonicalComparison (pairFst B S hS Y f i j) (pairSnd B S hS Y f i j) (f i) (f j)
          (pair_condition B S hS Y f i j) P).hom ≫
        (modulePullback B S hS (pairSnd B S hS Y f i j)).map (κ j).hom) :
    canonicalDescentDatum' B S hS Y f P hP ≅ canonicalDescentDatum' B S hS Y f Q hQ where
  hom := DescentDatum.Hom.mk (fun i ↦ (κ i).hom) hκ
  inv := DescentDatum.Hom.mk (fun i ↦ (κ i).inv) (fun i j ↦ by
    have hiso : (modulePullback B S hS (pairFst B S hS Y f i j)).mapIso (κ i) ≪≫
        canonicalComparison (pairFst B S hS Y f i j) (pairSnd B S hS Y f i j) (f i) (f j)
          (pair_condition B S hS Y f i j) Q =
        canonicalComparison (pairFst B S hS Y f i j) (pairSnd B S hS Y f i j) (f i) (f j)
          (pair_condition B S hS Y f i j) P ≪≫
        (modulePullback B S hS (pairSnd B S hS Y f i j)).mapIso (κ j) := Iso.ext (hκ i j)
    have := congrArg (fun z ↦ ((modulePullback B S hS (pairFst B S hS Y f i j)).mapIso
      (κ i)).symm ≪≫ z ≪≫ ((modulePullback B S hS (pairSnd B S hS Y f i j)).mapIso (κ j)).symm)
      hiso
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl] at this
    exact (congrArg Iso.hom this).symm)
  hom_inv_id := DescentDatum.Hom.ext fun i ↦ (κ i).hom_inv_id
  inv_hom_id := DescentDatum.Hom.ext fun i ↦ (κ i).inv_hom_id

namespace PicardSituation

namespace LocalTrivialization

variable {s : PicardSituation B S hS} {T : s.SchemesOver}
  {L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2}
  (t : s.LocalTrivialization T L) (h : s.StructureSheafMapIso)
  {N : Modules.{u, u} B S hS (s.baseSpaceAt T).1 (s.baseSpaceAt T).2}
  (hN : N.IsQuasicoherentOnSite)
  (e : t.descentDatum h ≅ canonicalDescentDatum' B S hS t.Y t.fY N hN)

/-- The components of an identification of the descent datum with a canonical one. -/
def α (i : t.I) : t.O i ≅ (modulePullback B S hS (t.fY i)).obj N where
  hom := e.hom.app i
  inv := e.inv.app i
  hom_inv_id := (DescentDatum.comp_app e.hom e.inv i).symm.trans
    ((congrArg (fun a : t.descentDatum h ⟶ t.descentDatum h ↦ a.app i) e.hom_inv_id).trans
      (DescentDatum.id_app _ i))
  inv_hom_id := (DescentDatum.comp_app e.inv e.hom i).symm.trans
    ((congrArg (fun a : canonicalDescentDatum' B S hS t.Y t.fY N hN ⟶
      canonicalDescentDatum' B S hS t.Y t.fY N hN ↦ a.app i) e.inv_hom_id).trans
      (DescentDatum.id_app _ i))

/-- The components `α` intertwine the transition isomorphisms with the canonical comparisons. -/
theorem α_naturality (i j : t.I) :
    (modulePullback B S hS (pairFst B S hS t.Y t.fY i j)).map (t.α h hN e i).hom ≫
        (canonicalComparison (pairFst B S hS t.Y t.fY i j) (pairSnd B S hS t.Y t.fY i j)
          (t.fY i) (t.fY j) (pair_condition B S hS t.Y t.fY i j) N).hom =
      (t.τ h i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS t.Y t.fY i j)).map (t.α h hN e j).hom :=
  e.hom.naturality i j

/-- The components `α` intertwine the transition isomorphisms with the canonical comparisons,
read on any test space. -/
theorem α_reading {Z : AlgebraicSpaces B S hS} (i j : t.I) (v : Z ⟶ pair B S hS t.Y t.fY i j)
    (vi : Z ⟶ t.Y i) (vj : Z ⟶ t.Y j) (hi : v ≫ pairFst B S hS t.Y t.fY i j = vi)
    (hj : v ≫ pairSnd B S hS t.Y t.fY i j = vj) (hc : vi ≫ t.fY i = vj ≫ t.fY j) :
    (modulePullback B S hS vi).mapIso (t.α h hN e i) ≪≫
        canonicalComparison vi vj (t.fY i) (t.fY j) hc N =
      transitionOn B S hS t.Y t.fY t.O (t.τ h) i j v vi vj hi hj ≪≫
        (modulePullback B S hS vj).mapIso (t.α h hN e j) := by
  subst hi hj
  have hpair : (modulePullback B S hS (pairFst B S hS t.Y t.fY i j)).mapIso (t.α h hN e i) ≪≫
      canonicalComparison (pairFst B S hS t.Y t.fY i j) (pairSnd B S hS t.Y t.fY i j)
        (t.fY i) (t.fY j) (pair_condition B S hS t.Y t.fY i j) N =
      t.τ h i j ≪≫ (modulePullback B S hS (pairSnd B S hS t.Y t.fY i j)).mapIso (t.α h hN e j) :=
    Iso.ext (t.α_naturality h hN e i j)
  have h₁ := congrArg (modulePullback B S hS v).mapIso hpair
  simp only [Functor.mapIso_trans] at h₁
  rw [modulePullback_mapIso_mapIso B S hS v _ _ rfl (t.α h hN e i),
    modulePullback_mapIso_mapIso B S hS v _ _ rfl (t.α h hN e j),
    modulePullback_mapIso_canonicalComparison B S hS v _ _ (t.fY i) (t.fY j)
      (pair_condition B S hS t.Y t.fY i j) _ _ rfl rfl hc N] at h₁
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc] at h₁
  have h₂ := congrArg (fun z ↦ pullbackComparison B S hS v (pairFst B S hS t.Y t.fY i j) _ rfl
    (t.O i) ≪≫ z ≪≫ (pullbackComparison B S hS v (pairSnd B S hS t.Y t.fY i j) _ rfl
      ((modulePullback B S hS (t.fY j)).obj N)).symm) h₁
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl] at h₂
  rw [transitionOn]
  simp only [Iso.trans_assoc]
  exact h₂

/-! ### Comparing the inverse image of the descended module with `L` -/

/-- The ratio of trivializations on the overlap of the base-changed family, expressed through the
descended module. -/
theorem ρ_eq_of_descent (i j : t.I) (vi : pair B S hS t.Y' t.f' i j ⟶ t.Y i)
    (vj : pair B S hS t.Y' t.f' i j ⟶ t.Y j)
    (hvi : pairFst B S hS t.Y' t.f' i j ≫ t.hh i = vi)
    (hvj : pairSnd B S hS t.Y' t.f' i j ≫ t.hh j = vj) (hc : vi ≫ t.fY i = vj ≫ t.fY j) :
    t.ρ (pairFst B S hS t.Y' t.f' i j) (pairSnd B S hS t.Y' t.f' i j)
        (pair_condition B S hS t.Y' t.f' i j) =
      (pullbackComparison B S hS _ (t.hh i) vi hvi _).symm ≪≫
        (modulePullback B S hS vi).mapIso (t.α h hN e i) ≪≫
        canonicalComparison vi vj (t.fY i) (t.fY j) hc N ≪≫
        ((modulePullback B S hS vj).mapIso (t.α h hN e j)).symm ≪≫
        pullbackComparison B S hS _ (t.hh j) vj hvj _ := by
  obtain ⟨G, hGi, hGj⟩ : ∃ G : pair B S hS t.Y' t.f' i j ⟶ pair B S hS t.Y t.fY i j,
      G ≫ pairFst B S hS t.Y t.fY i j = vi ∧ G ≫ pairSnd B S hS t.Y t.fY i j = vj :=
    ⟨_, (AlgebraicSpaces.isPullback_fiberProduct B S hS (t.fY i) (t.fY j)).lift_fst _ _ hc,
      (AlgebraicSpaces.isPullback_fiberProduct B S hS (t.fY i) (t.fY j)).lift_snd _ _ hc⟩
  have hKR := t.transitionOn_τ h (pairFst B S hS t.Y' t.f' i j) (pairSnd B S hS t.Y' t.f' i j)
    (pair_condition B S hS t.Y' t.f' i j) G vi vj hGi hGj hvi hvj
  have hK2 := t.α_reading h hN e i j G vi vj hGi hGj hc
  rw [hKR] at hK2
  have h₃ := congrArg (fun z ↦ (pullbackComparison B S hS _ (t.hh i) vi hvi _).symm ≪≫ z ≪≫
    ((modulePullback B S hS vj).mapIso (t.α h hN e j)).symm ≪≫
      pullbackComparison B S hS _ (t.hh j) vj hvj _) hK2
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc] at h₃
  dsimp only [O] at h₃ ⊢
  simp only [Iso.symm_self_id, Iso.trans_refl] at h₃
  exact h₃.symm

/-- The comparison of the inverse image of the descended module with `L` on the base change of
a member of the family. -/
def κ (i : t.I) :
    (modulePullback B S hS (t.f' i)).obj
        ((modulePullback B S hS (baseChangeInclusion s.f T)).obj N) ≅
      (modulePullback B S hS (t.f' i)).obj L :=
  canonicalComparison (t.f' i) (t.hh i) (baseChangeInclusion s.f T) (t.fY i)
      (t.f'_comp_inclusion i) N ≪≫
    (modulePullback B S hS (t.hh i)).mapIso (t.α h hN e i).symm ≪≫ t.β i

/-- The two composites from the overlap of the base-changed family to the test scheme agree. -/
theorem pair_hc (i j : t.I) :
    (pairFst B S hS t.Y' t.f' i j ≫ t.hh i) ≫ t.fY i =
      (pairSnd B S hS t.Y' t.f' i j ≫ t.hh j) ≫ t.fY j := by
  rw [Category.assoc, ← t.f'_comp_inclusion, ← Category.assoc, pair_condition, Category.assoc,
    t.f'_comp_inclusion, Category.assoc]

/-- **The comparisons `κ` are compatible with the canonical descent data** of the inverse image
of the descended module and of `L`. -/
theorem κ_naturality (i j : t.I) :
    (modulePullback B S hS (pairFst B S hS t.Y' t.f' i j)).mapIso (t.κ h hN e i) ≪≫
        canonicalComparison (pairFst B S hS t.Y' t.f' i j) (pairSnd B S hS t.Y' t.f' i j)
          (t.f' i) (t.f' j) (pair_condition B S hS t.Y' t.f' i j) L =
      canonicalComparison (pairFst B S hS t.Y' t.f' i j) (pairSnd B S hS t.Y' t.f' i j)
          (t.f' i) (t.f' j) (pair_condition B S hS t.Y' t.f' i j)
          ((modulePullback B S hS (baseChangeInclusion s.f T)).obj N) ≪≫
        (modulePullback B S hS (pairSnd B S hS t.Y' t.f' i j)).mapIso (t.κ h hN e j) := by
  have hρ := t.ρ_eq_of_descent h hN e i j _ _ rfl rfl (t.pair_hc i j)
  have hL : canonicalComparison (pairFst B S hS t.Y' t.f' i j) (pairSnd B S hS t.Y' t.f' i j)
      (t.f' i) (t.f' j) (pair_condition B S hS t.Y' t.f' i j) L =
      ((modulePullback B S hS (pairFst B S hS t.Y' t.f' i j)).mapIso (t.β i)).symm ≪≫
        t.ρ (pairFst B S hS t.Y' t.f' i j) (pairSnd B S hS t.Y' t.f' i j)
          (pair_condition B S hS t.Y' t.f' i j) ≪≫
        (modulePullback B S hS (pairSnd B S hS t.Y' t.f' i j)).mapIso (t.β j) := by
    simp only [ρ, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  rw [hL, hρ]
  simp only [κ, Functor.mapIso_trans, Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [modulePullback_mapIso_mapIso B S hS (pairFst B S hS t.Y' t.f' i j) (t.hh i) _ rfl
      (t.α h hN e i).symm,
    modulePullback_mapIso_mapIso B S hS (pairSnd B S hS t.Y' t.f' i j) (t.hh j) _ rfl
      (t.α h hN e j).symm]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Functor.mapIso_symm, Iso.symm_self_id_assoc]
  exact canonicalComparison_squares_assoc (pairFst B S hS t.Y' t.f' i j)
    (pairSnd B S hS t.Y' t.f' i j) (t.f' i) (t.f' j) (baseChangeInclusion s.f T) (t.hh i)
    (t.hh j) (t.fY i) (t.fY j) (t.f'_comp_inclusion i) (t.f'_comp_inclusion j)
    (pair_condition B S hS t.Y' t.f' i j) (t.pair_hc i j) N _

/-- `κ_naturality`, on the underlying morphisms. -/
theorem κ_naturality_hom (i j : t.I) :
    (modulePullback B S hS (pairFst B S hS t.Y' t.f' i j)).map (t.κ h hN e i).hom ≫
        (canonicalComparison (pairFst B S hS t.Y' t.f' i j) (pairSnd B S hS t.Y' t.f' i j)
          (t.f' i) (t.f' j) (pair_condition B S hS t.Y' t.f' i j) L).hom =
      (canonicalComparison (pairFst B S hS t.Y' t.f' i j) (pairSnd B S hS t.Y' t.f' i j)
          (t.f' i) (t.f' j) (pair_condition B S hS t.Y' t.f' i j)
          ((modulePullback B S hS (baseChangeInclusion s.f T)).obj N)).hom ≫
        (modulePullback B S hS (pairSnd B S hS t.Y' t.f' i j)).map (t.κ h hN e j).hom := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom] using congrArg Iso.hom (t.κ_naturality h hN e i j)

/-! ### The descended module -/

/-- **The descended module is invertible**: its inverse images along the covering family are
the structure sheaves of the members. -/
theorem isInvertibleModule_descended
    (e : t.descentDatum h ≅ canonicalDescentDatum' B S hS t.Y t.fY N hN)
    (hcov : IsFpqcCovering B S hS fun i ↦ (t.fY i).hom) :
    IsInvertibleModule (s.baseSpaceAt T) N :=
  isInvertibleModule_of_isFpqcCovering_of_isQuasicoherentOnSite t.fY hcov N hN fun i ↦
    isInvertibleModule_of_iso (t.α h hN e i) (isInvertibleModule_structureModule _)

/-- **The inverse image of the descended module to `X_T` is `L`.** -/
theorem nonempty_iso_descended (e : t.descentDatum h ≅ canonicalDescentDatum' B S hS t.Y t.fY N hN)
    (hcov : IsFpqcCovering B S hS fun i ↦ (t.fY i).hom)
    (hL : IsInvertibleModule (s.baseChange T) L) :
    Nonempty ((modulePullback B S hS (baseChangeInclusion s.f T)).obj N ≅ L) := by
  have hLqc := isQuasicoherentOnSite_of_isInvertibleModule _ L hL
  have hN'qc := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (baseChangeInclusion s.f T) N hN
  obtain ⟨hff⟩ := nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering B S hS
    t.Y' t.f' (isFpqcCovering_baseChangeMap s.f t.g hcov)
  let E : canonicalDescentDatum' B S hS t.Y' t.f'
      ((modulePullback B S hS (baseChangeInclusion s.f T)).obj N) hN'qc ≅
      canonicalDescentDatum' B S hS t.Y' t.f' L hLqc :=
    canonicalDescentDatumIsoMk (Y := t.Y') (f := t.f') hN'qc hLqc (t.κ h hN e)
      (t.κ_naturality_hom h hN e)
  exact ⟨(ObjectProperty.ι _).mapIso (hff.preimageIso (X := ⟨_, hN'qc⟩) (Y := ⟨L, hLqc⟩) E)⟩

end LocalTrivialization

end PicardSituation

end AlgebraicGeometry.Space

end

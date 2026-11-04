module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.IndexRhoNaturality
public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.CechSections

/-!
# Morphisms of glueing data from the low-degree summands of the Čech object

Let `(C, O_C)` be a ringed site with fibre products, `f_i : U_i ⟶ X` a family of arrows, and
`(E_i, ρ_{ij})`, `(E'_i, ρ'_{ij})` two families of derived objects on the `U_i` with
isomorphisms on the overlaps satisfying the cocycle condition. Suppose given isomorphisms of the
locally given objects of the two families on the summands of degrees `0` and `1` of the Čech
object, compatible with the isomorphisms `ρ_g` along the two faces of the summands of degree
`1`. Restricting the isomorphisms of degree `0` along the sections `U_i ⟶ U_i` of the one-fold
products gives isomorphisms `β_i : E'_i ≅ E_i` carrying `ρ'_{ij}` to `ρ_{ij}`: on `U_{ij}`, both
restrictions of `β_i` and of `β_j` are restrictions of the isomorphism of degree `1`, up to the
isomorphisms attached to the overlaps.

## Main results

* `AlgebraicGeometry.RingedSite.CoveringGlueing.exists_iso_of_cech`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CategoryTheory.Functor

/-- For a functor isomorphic to the identity, the image of the morphism obtained by conjugating
`R : F A ⟶ F B` with the isomorphism is `R`. -/
theorem map_conj_eq {𝒞 : Type*} [Category 𝒞] (F : 𝒞 ⥤ 𝒞) (e : F ≅ 𝟭 𝒞) {A B : 𝒞}
    (R : F.obj A ⟶ F.obj B) : F.map (e.inv.app A ≫ R ≫ e.hom.app B) = R := by
  rw [← cancel_mono (e.hom.app B)]
  have n : F.map (e.inv.app A ≫ R ≫ e.hom.app B) ≫ e.hom.app B =
      e.hom.app A ≫ e.inv.app A ≫ R ≫ e.hom.app B :=
    e.hom.naturality (e.inv.app A ≫ R ≫ e.hom.app B)
  rw [n, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Functor

namespace CategoryTheory

/-- The diagram chase of the compatibility of the restrictions of `β_i` and `β_j` with the
isomorphisms on an overlap. -/
theorem overlap_chase {𝒞 : Type*} [Category 𝒞] {a b a' b' : 𝒞} (x : a' ⟶ a) (y : b' ⟶ b)
    (R x₀ : a' ⟶ a) (y₀ : b' ⟶ b) (ι : a ⟶ a) (ι' : a' ⟶ a') (ω₁ : a ⟶ b) (ω₂ : b ⟶ a)
    (ω₁' : a' ⟶ b') (ω₂' : b' ⟶ a') (hx : x₀ = x) (hy : y₀ = y) (r₀ : x₀ ≫ ι = ι' ≫ R)
    (hι : ι = 𝟙 a) (hι' : ι' = 𝟙 a') (r₁ : y₀ ≫ ω₂ = ω₂' ≫ R) (h₁ : ω₂ ≫ ω₁ = 𝟙 b)
    (h₂ : ω₁' ≫ ω₂' = 𝟙 a') :
    x ≫ ω₁ = ω₁' ≫ y := by
  subst hx hy hι hι'
  rw [Category.comp_id, Category.id_comp] at r₀
  rw [r₀, ← Category.id_comp (R ≫ ω₁), ← h₂, Category.assoc, ← reassoc_of% r₁, h₁,
    Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSite.{u, u, u}} [HasPullbacks X.C] {X₀ : X.C} {ι : Type u} {U : ι → X.C}
  (f : ∀ i, U i ⟶ X₀) {E E' : ∀ i, LocalDerivedCategory.{0} X (U i)}
  (ρ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E i) ≅
    (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j))
  (ρ' : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E' i) ≅
    (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E' j))

/-- Compatibility with `indexRhoBase` is compatibility of a restriction with an isomorphism
attached to an overlap. -/
theorem indexRhoBase_comm_iff {b b' : IndexCategory f} (g : b' ⟶ b)
    (θ : (derivedOverMap.{0} X b.a).obj (E' b.i) ⟶ (derivedOverMap.{0} X b.a).obj (E b.i))
    (θ' : (derivedOverMap.{0} X b'.a).obj (E' b'.i) ⟶ (derivedOverMap.{0} X b'.a).obj (E b'.i)) :
    (derivedOverMap.{0} X g.hom.left).map θ ≫ (indexRhoBase f E ρ g).hom =
        (indexRhoBase f E' ρ' g).hom ≫ θ' ↔
      restrictAlong b.a g.hom.left rfl θ ≫
          (overlapIso f ρ (g.hom.left ≫ b.a) b'.a (Index.comp_w g)).hom =
        (overlapIso f ρ' (g.hom.left ≫ b.a) b'.a (Index.comp_w g)).hom ≫ θ' := by
  simp only [indexRhoBase, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, restrictAlong,
    Category.assoc]
  rw [← cancel_epi ((derivedOverMapComp.{0} X
    (rfl : g.hom.left ≫ b.a = g.hom.left ≫ b.a)).inv.app (E' b.i)), Iso.inv_hom_id_app_assoc]

/-- The isomorphism `β_i : E'_i ≅ E_i` obtained by restricting an isomorphism of the locally
given objects on the summand of degree `0` attached to `i` along the section
`U_i ⟶ U_i`. -/
def cechVertexIso (i : ι)
    (θ : (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).obj (E' i) ≅
      (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).obj (E i)) :
    E' i ≅ E i :=
  ((X.derivedOverMapIdIso (U i)).app (E' i)).symm ≪≫
    restrictAlongIso _ (cechVertexSection f i) (cechVertexSection_comp f i) θ ≪≫
      (X.derivedOverMapIdIso (U i)).app (E i)

/-- The restrictions of `β_i` are the restrictions of the isomorphism on the summand of degree
`0`. -/
theorem restrictAlong_cechVertexSection {i : ι}
    (θ : (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).obj (E' i) ≅
      (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).obj (E i))
    {W : X.C} (h : W ⟶ U i)
    (hy : (h ≫ cechVertexSection f i) ≫ (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a = h) :
    restrictAlong _ (h ≫ cechVertexSection f i) hy θ.hom =
      (derivedOverMap.{0} X h).map (cechVertexIso f i θ).hom := by
  have hh : h ≫ 𝟙 (U i) = h := Category.comp_id h
  refine (restrictAlong_comp_left _ (cechVertexSection f i) (cechVertexSection_comp f i) h hh
    hy θ.hom).trans ?_
  refine (congrArg (fun z => (derivedOverMapComp.{0} X hh).hom.app (E' i) ≫
    (derivedOverMap.{0} X h).map z ≫ (derivedOverMapComp.{0} X hh).inv.app (E i))
      (Functor.map_conj_eq _ (X.derivedOverMapIdIso (U i)) _).symm).trans ?_
  exact restrictAlong_map (𝟙 (U i)) h hh (cechVertexIso f i θ).hom

/-- A morphism equal to a composite with the section of the summand of degree `0` is a section
of the structure arrow over its first factor. -/
private theorem comp_eq_of_eq_cechVertexSection {i : ι} {W : X.C} {h : W ⟶ U i}
    {c : W ⟶ ((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i) |>.V.left}
    (hc : c = h ≫ cechVertexSection f i) :
    c ≫ (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a = h := by
  rw [hc, Category.assoc]
  exact (congrArg (h ≫ ·) (cechVertexSection_comp f i)).trans (Category.comp_id h)

/-- Restriction of the isomorphism of degree `0` along any morphism equal to a composite with
the section is the restriction of `β_i`. -/
private theorem restrictAlong_eq_map_cechVertexIso {i : ι}
    (θ : (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).obj (E' i) ≅
      (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).obj (E i))
    {W : X.C} (h : W ⟶ U i) {c : W ⟶ ((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i) |>.V.left}
    (hc : c = h ≫ cechVertexSection f i)
    (hz : c ≫ (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a = h) :
    restrictAlong _ c hz θ.hom = (derivedOverMap.{0} X h).map (cechVertexIso f i θ).hom := by
  subst hc
  exact restrictAlong_cechVertexSection f θ h hz

variable {f ρ ρ'} in
/-- **Isomorphisms of the locally given objects on the summands of degrees `0` and `1` of the
Čech object, compatible with the faces, give an isomorphism of glueing data.** -/
theorem cechVertexIso_compatible (hρ : IsCocycle f ρ) (hρ' : IsCocycle f ρ')
    (θ₀ : ∀ i, (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).obj
        (E' i) ≅ (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).obj
          (E i))
    (θ₁ : ∀ i j, (derivedOverMap.{0} X (((cechLift f).obj (op ⦋1⦌)).obj (cechEdge f i j)).a).obj
        (E' i) ≅ (derivedOverMap.{0} X (((cechLift f).obj (op ⦋1⦌)).obj (cechEdge f i j)).a).obj
          (E i))
    (h₀ : ∀ i j, (derivedOverMap.{0} X (cechEdgeFace f i j 0).hom.left).map (θ₀ i).hom ≫
        (indexRhoBase f E ρ (cechEdgeFace f i j 0)).hom =
      (indexRhoBase f E' ρ' (cechEdgeFace f i j 0)).hom ≫ (θ₁ i j).hom)
    (h₁ : ∀ i j, (derivedOverMap.{0} X (cechEdgeFace f i j 1).hom.left).map (θ₀ j).hom ≫
        (indexRhoBase f E ρ (cechEdgeFace f i j 1)).hom =
      (indexRhoBase f E' ρ' (cechEdgeFace f i j 1)).hom ≫ (θ₁ i j).hom)
    (i j : ι) :
    (derivedOverMap.{0} X (pullback.fst (f i) (f j))).map (cechVertexIso f i (θ₀ i)).hom ≫
        (ρ i j).hom =
      (ρ' i j).hom ≫ (derivedOverMap.{0} X (pullback.snd (f i) (f j))).map
        (cechVertexIso f j (θ₀ j)).hom := by
  have hx : cechEdgeLift f i j ≫ (((cechLift f).obj (op ⦋1⦌)).obj (cechEdge f i j)).a =
      pullback.fst (f i) (f j) := cechEdgeLift_comp f i j
  have hz₀ := comp_eq_of_eq_cechVertexSection f (cechEdgeLift_comp_face_zero f i j)
  have hz₁ := comp_eq_of_eq_cechVertexSection f (cechEdgeLift_comp_face_one f i j)
  have r₀ := restrictAlong_overlapIso f ρ ρ' _ _ _ _ _ _
    ((indexRhoBase_comm_iff f ρ ρ' (cechEdgeFace f i j 0) _ _).1 (h₀ i j)) (cechEdgeLift f i j)
    hz₀ hx rfl
  have r₁ := restrictAlong_overlapIso f ρ ρ' _ _ _ _ _ _
    ((indexRhoBase_comm_iff f ρ ρ' (cechEdgeFace f i j 1) _ _).1 (h₁ i j)) (cechEdgeLift f i j)
    hz₁ hx pullback.condition.symm
  rw [← overlapIso_fst_snd f ρ, ← overlapIso_fst_snd f ρ']
  exact overlap_chase _ _ _ _ _ _ _ _ _ _ _
    (restrictAlong_eq_map_cechVertexIso f (θ₀ i) _ (cechEdgeLift_comp_face_zero f i j) hz₀)
    (restrictAlong_eq_map_cechVertexIso f (θ₀ j) _ (cechEdgeLift_comp_face_one f i j) hz₁)
    r₀ (overlapIso_self f ρ hρ _ _) (overlapIso_self f ρ' hρ' _ _) r₁
    (overlapIso_symm f ρ hρ _ _ pullback.condition.symm pullback.condition)
    (overlapIso_symm f ρ' hρ' _ _ pullback.condition pullback.condition.symm)

/-- **Restriction to the summand of degree `0` attached to `i` is faithful**: it has the section
`U_i ⟶ U_i`. -/
theorem derivedOverMap_cechVertex_map_injective {i : ι} {A B : LocalDerivedCategory.{0} X (U i)}
    {x y : A ⟶ B}
    (h : (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).map x =
      (derivedOverMap.{0} X (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a).map y) :
    x = y := by
  have e : (derivedOverMap.{0} X (𝟙 (U i))).map x = (derivedOverMap.{0} X (𝟙 (U i))).map y :=
    (restrictAlong_map _ (cechVertexSection f i) (cechVertexSection_comp f i) x).symm.trans
      ((congrArg (restrictAlong _ (cechVertexSection f i) (cechVertexSection_comp f i)) h).trans
        (restrictAlong_map _ (cechVertexSection f i) (cechVertexSection_comp f i) y))
  have : (derivedOverMap.{0} X (𝟙 (U i))).Faithful :=
    Functor.Faithful.of_iso (X.derivedOverMapIdIso (U i)).symm
  exact (derivedOverMap.{0} X (𝟙 (U i))).map_injective e

end AlgebraicGeometry.RingedSite.CoveringGlueing

end

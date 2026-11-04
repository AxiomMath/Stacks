module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistMap
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistTransport
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.NormalizedPullback

/-!
# The map `θ` of Tag 07ZG on two charts of `U(ψ)`, compared

Let `e : C ⟶ U(ψ)` and `e' : C' ⟶ U(ψ')` be charts lying over `P ⟶ Proj(A)`, `Q ⟶ Proj(B)` and
`P' ⟶ Proj(A')`, `Q' ⟶ Proj(B')`, and let `j : C' ⟶ C`, `y_P : P' ⟶ P`, `y_Q : Q' ⟶ Q` and
`k : U(ψ') ⟶ U(ψ)` form commutative squares over morphisms `c_A`, `c_B` of the relative Projs
carrying the twists to the twists (`χ_A`, `χ_B`). Then the chart map of the transport of `θ` along
`k` is the pullback along `j` of the chart map of `θ`, read through the comparisons of the twists
along `y_P` and `y_Q` (`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_transport`). This is
pure coherence of the inverse image: the pseudofunctoriality isomorphisms and the identifications
along equal morphisms.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom_app`: the transport in degree `n`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_eq`: the chart map written out.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_transport`: the comparison of the chart
  maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Scheme.Modules (pullback pullbackComp pullbackCongr)
open Stacks.Picard (pullbackCompEq pullbackCompEq_assoc pullbackCompEq_rfl)

universe u

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

/-! ### Coherence of the inverse image along two squares -/

section Coherence

variable {X Y Z W : Scheme.{u}}

/-- Folding a contraction followed by an identification along an equality. -/
private theorem fold_hom (f : X ⟶ Y) (g : Y ⟶ Z) {c : X ⟶ Z} (h : f ≫ g = c) (M : Z.Modules)
    {N : X.Modules} (z : (pullback c).obj M ⟶ N) :
    (pullbackComp f g).hom.app M ≫ (pullbackCongr h).hom.app M ≫ z =
      (pullbackCompEq f g c h).hom.app M ≫ z :=
  (Category.assoc _ _ _).symm

/-- Folding a contraction followed by an identification along an equality, inside a pullback. -/
private theorem fold_map_hom (t : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) {c : X ⟶ Z} (h : f ≫ g = c)
    (M : Z.Modules) {N : W.Modules} (z : (pullback t).obj ((pullback c).obj M) ⟶ N) :
    (pullback t).map ((pullbackComp f g).hom.app M) ≫
        (pullback t).map ((pullbackCongr h).hom.app M) ≫ z =
      (pullback t).map ((pullbackCompEq f g c h).hom.app M) ≫ z := by
  rw [← Functor.map_comp_assoc]
  rfl

/-- Folding the inverse of an identification followed by the inverse of a contraction. -/
private theorem fold_inv (f : X ⟶ Y) (g : Y ⟶ Z) {c : X ⟶ Z} (h : f ≫ g = c) (M : Z.Modules)
    {N : X.Modules} (z : (pullback f).obj ((pullback g).obj M) ⟶ N) :
    (pullbackCongr h).inv.app M ≫ (pullbackComp f g).inv.app M ≫ z =
      (pullbackCompEq f g c h).inv.app M ≫ z :=
  (Category.assoc _ _ _).symm

/-- Folding the inverse of an identification followed by the inverse of a contraction, inside a
pullback. -/
private theorem fold_map_inv (t : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) {c : X ⟶ Z} (h : f ≫ g = c)
    (M : Z.Modules) {N : W.Modules}
    (z : (pullback t).obj ((pullback f).obj ((pullback g).obj M)) ⟶ N) :
    (pullback t).map ((pullbackCongr h).inv.app M) ≫
        (pullback t).map ((pullbackComp f g).inv.app M) ≫ z =
      (pullback t).map ((pullbackCompEq f g c h).inv.app M) ≫ z := by
  rw [← Functor.map_comp_assoc]
  rfl

/-- The image of the inverse of a component followed by the image of the component. -/
private theorem map_inv_hom_app_assoc {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {G H : X.Modules ⥤ 𝒞} (α : G ≅ H) (M : X.Modules) {N : 𝒟} (z : F.obj (H.obj M) ⟶ N) :
    F.map (α.inv.app M) ≫ F.map (α.hom.app M) ≫ z = z := by
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The comparison of a contraction along two names `c`, `c'` of the same composite. -/
private theorem pullbackCompEq_comp_pullbackCompEq (f : X ⟶ Y) (g : Y ⟶ Z) (l : Z ⟶ W)
    {c c' : X ⟶ Z} (h : f ≫ g = c) (h' : f ≫ g = c') {w : X ⟶ W} (e₁ : c ≫ l = w)
    (e₂ : c' ≫ l = w) (M : W.Modules) :
    (pullbackCompEq f g c h).hom.app ((pullback l).obj M) ≫ (pullbackCompEq c l w e₁).hom.app M =
      (pullbackCompEq f g c' h').hom.app ((pullback l).obj M) ≫
        (pullbackCompEq c' l w e₂).hom.app M := by
  subst h h'
  rfl

variable {C C' P P' Y' U U' : Scheme.{u}}

/-- **The left half of the comparison of the chart maps**: along the squares of `j`, `y_P` and
`k`, the identifications from `j^*a^*p^*M` to `e'^*k^*r^*M` agree, once the comparison `χ` of
`c_A^*M` with `M'` is undone. -/
private theorem legL (j : C' ⟶ C) (a : C ⟶ P) (p : P ⟶ Y) (a' : C' ⟶ P') (yP : P' ⟶ P)
    (p' : P' ⟶ Y') (cA : Y' ⟶ Y) (e : C ⟶ U) (r : U ⟶ Y) (e' : C' ⟶ U') (r' : U' ⟶ Y')
    (k : U' ⟶ U) (ha : a ≫ p = e ≫ r) (ha' : a' ≫ p' = e' ≫ r') (hr : r' ≫ cA = k ≫ r)
    (hjA : j ≫ a = a' ≫ yP) (hyP : yP ≫ p = p' ≫ cA) (hk : e' ≫ k = j ≫ e) (M : Y.Modules)
    {M' : Y'.Modules} (χ : (pullback cA).obj M ≅ M') :
    (pullbackComp j a).hom.app ((pullback p).obj M) ≫
        (pullbackCongr hjA).hom.app ((pullback p).obj M) ≫
        (pullbackComp a' yP).inv.app ((pullback p).obj M) ≫
        (pullback a').map ((pullbackComp yP p).hom.app M) ≫
        (pullback a').map ((pullbackCongr hyP).hom.app M) ≫
        (pullback a').map ((pullbackComp p' cA).inv.app M) ≫
        (pullback a').map ((pullback p').map χ.hom) ≫
        (pullbackComp a' p').hom.app M' ≫ (pullbackCongr ha').hom.app M' ≫
        (pullbackComp e' r').inv.app M' ≫
        (pullback e').map ((pullback r').map χ.inv) ≫
        (pullback e').map ((pullbackComp r' cA).hom.app M) ≫
        (pullback e').map ((pullbackCongr hr).hom.app M) ≫
        (pullback e').map ((pullbackComp k r).inv.app M) =
      (pullback j).map ((pullbackComp a p).hom.app M) ≫
        (pullback j).map ((pullbackCongr ha).hom.app M) ≫
        (pullback j).map ((pullbackComp e r).inv.app M) ≫
        (pullbackComp j e).hom.app ((pullback r).obj M) ≫
        (pullbackCongr hk.symm).hom.app ((pullback r).obj M) ≫
        (pullbackComp e' k).inv.app ((pullback r).obj M) := by
  -- move `χ` across the contraction along `a' ≫ p' = e' ≫ r'`, where it cancels
  have hη := ((pullbackComp a' p') ≪≫ pullbackCongr ha' ≪≫ (pullbackComp e' r').symm).hom.naturality
    χ.hom
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc] at hη
  rw [reassoc_of% hη, ← Functor.map_comp_assoc ((pullback e')) ((pullback r').map χ.hom),
    ← Functor.map_comp (pullback r'), Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id,
    Category.id_comp]
  -- the pure coherence, checked after the identification along `e' ≫ k ≫ r = j ≫ a ≫ p`
  have hW : e' ≫ k ≫ r = j ≫ a ≫ p := by rw [← Category.assoc, hk, Category.assoc, ← ha]
  refine (cancel_mono ((pullback e').map ((pullbackComp k r).hom.app M) ≫
    (pullbackCompEq e' (k ≫ r) (j ≫ a ≫ p) hW).hom.app M)).1 ?_
  simp only [Category.assoc, fold_hom, fold_map_hom]
  have h2 : (e' ≫ r') ≫ cA = j ≫ a ≫ p := by rw [Category.assoc, hr]; exact hW
  have h4 : (a' ≫ p') ≫ cA = j ≫ a ≫ p := by rw [ha']; exact h2
  have h5 : a' ≫ p' ≫ cA = j ≫ a ≫ p := by rw [← Category.assoc]; exact h4
  have h7 : (a' ≫ yP) ≫ p = j ≫ a ≫ p := by rw [Category.assoc, hyP]; exact h5
  have ht1 : (e' ≫ k) ≫ r = j ≫ a ≫ p := by rw [Category.assoc]; exact hW
  have ht3 : j ≫ e ≫ r = j ≫ a ≫ p := by rw [← ha]
  have ht5 : (j ≫ a) ≫ p = j ≫ a ≫ p := Category.assoc _ _ _
  have s2 := pullbackCompEq_assoc e' r' cA (k ≫ r) (e' ≫ r') (j ≫ a ≫ p) hr rfl hW h2 M
  have s4 := pullbackCompEq_comp_pullbackCompEq a' p' cA ha' rfl h2 h4 M
  have s5 := pullbackCompEq_assoc a' p' cA (p' ≫ cA) (a' ≫ p') (j ≫ a ≫ p) rfl rfl h5 h4 M
  have s7 := pullbackCompEq_assoc a' yP p (p' ≫ cA) (a' ≫ yP) (j ≫ a ≫ p) hyP rfl h5 h7 M
  have s9 := pullbackCompEq_assoc j a p (a ≫ p) (a' ≫ yP) (j ≫ a ≫ p) rfl hjA rfl h7 M
  have t1 := pullbackCompEq_assoc e' k r (k ≫ r) (e' ≫ k) (j ≫ a ≫ p) rfl rfl hW ht1 M
  have t3 := pullbackCompEq_assoc j e r (e ≫ r) (e' ≫ k) (j ≫ a ≫ p) rfl hk.symm ht3 ht1 M
  have t5 := pullbackCompEq_assoc j a p (e ≫ r) (j ≫ a) (j ≫ a ≫ p) ha rfl ht3 ht5 M
  have t6 := pullbackCompEq_assoc j a p (a ≫ p) (j ≫ a) (j ≫ a ≫ p) rfl rfl rfl ht5 M
  simp only [pullbackCompEq_rfl] at s2 s4 s5 s7 s9 t1 t3 t5 t6
  rw [map_inv_hom_app_assoc, s2, Iso.inv_hom_id_app_assoc, s4, ← s5, map_inv_hom_app_assoc, s7,
    Iso.inv_hom_id_app_assoc, ← s9, t1, Iso.inv_hom_id_app_assoc, ← t3, map_inv_hom_app_assoc, t5,
    ← t6]

/-- **The right half of the comparison of the chart maps**: along the squares of `j`, `y_Q` and
`k`, the identifications from `j^*e^*ι^*N` to `b'^*q'^*N'` agree. -/
private theorem legR (j : C' ⟶ C) (e : C ⟶ U) (ι : U ⟶ Y) (e' : C' ⟶ U') (ι' : U' ⟶ Y')
    (k : U' ⟶ U) (cB : Y' ⟶ Y) (b : C ⟶ P) (q : P ⟶ Y) (b' : C' ⟶ P') (q' : P' ⟶ Y')
    (yQ : P' ⟶ P) (hb : b ≫ q = e ≫ ι) (hb' : b' ≫ q' = e' ≫ ι') (hι : k ≫ ι = ι' ≫ cB)
    (hjB : j ≫ b = b' ≫ yQ) (hyQ : yQ ≫ q = q' ≫ cB) (hk : e' ≫ k = j ≫ e) (N : Y.Modules)
    {N' : Y'.Modules} (χ : (pullback cB).obj N ≅ N') :
    (pullbackComp j e).hom.app ((pullback ι).obj N) ≫
        (pullbackCongr hk.symm).hom.app ((pullback ι).obj N) ≫
        (pullbackComp e' k).inv.app ((pullback ι).obj N) ≫
        (pullback e').map ((pullbackComp k ι).hom.app N) ≫
        (pullback e').map ((pullbackCongr hι).hom.app N) ≫
        (pullback e').map ((pullbackComp ι' cB).inv.app N) ≫
        (pullback e').map ((pullback ι').map χ.hom) ≫
        (pullbackComp e' ι').hom.app N' ≫ (pullbackCongr hb').inv.app N' ≫
        (pullbackComp b' q').inv.app N' =
      (pullback j).map ((pullbackComp e ι).hom.app N) ≫
        (pullback j).map ((pullbackCongr hb).inv.app N) ≫
        (pullback j).map ((pullbackComp b q).inv.app N) ≫
        (pullbackComp j b).hom.app ((pullback q).obj N) ≫
        (pullbackCongr hjB).hom.app ((pullback q).obj N) ≫
        (pullbackComp b' yQ).inv.app ((pullback q).obj N) ≫
        (pullback b').map ((pullbackComp yQ q).hom.app N) ≫
        (pullback b').map ((pullbackCongr hyQ).hom.app N) ≫
        (pullback b').map ((pullbackComp q' cB).inv.app N) ≫
        (pullback b').map ((pullback q').map χ.hom) := by
  -- move `χ` across the contraction along `e' ≫ ι' = b' ≫ q'` to the end
  have hη := ((pullbackComp e' ι') ≪≫ (pullbackCongr hb').symm ≪≫
    (pullbackComp b' q').symm).hom.naturality χ.hom
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc] at hη
  rw [hη]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  -- the pure coherence, checked after the identification along `b' ≫ q' ≫ c_B = j ≫ e ≫ ι`
  have hW : b' ≫ q' ≫ cB = j ≫ e ≫ ι := by
    rw [← hyQ, ← Category.assoc, ← hjB, Category.assoc, hb]
  refine (cancel_mono ((pullback b').map ((pullbackComp q' cB).hom.app N) ≫
    (pullbackCompEq b' (q' ≫ cB) (j ≫ e ≫ ι) hW).hom.app N)).1 ?_
  simp only [Category.assoc, fold_hom, fold_map_hom, fold_inv, fold_map_inv]
  have hu1 : (b' ≫ q') ≫ cB = j ≫ e ≫ ι := by rw [Category.assoc]; exact hW
  have hu1' : (e' ≫ ι') ≫ cB = j ≫ e ≫ ι := by rw [← hb']; exact hu1
  have hu3 : e' ≫ ι' ≫ cB = j ≫ e ≫ ι := by rw [← Category.assoc]; exact hu1'
  have hu5 : (e' ≫ k) ≫ ι = j ≫ e ≫ ι := by rw [hk, Category.assoc]
  have hv1 : (b' ≫ yQ) ≫ q = j ≫ e ≫ ι := by rw [Category.assoc, hyQ]; exact hW
  have u1 := pullbackCompEq_assoc b' q' cB (q' ≫ cB) (b' ≫ q') (j ≫ e ≫ ι) rfl rfl hW hu1 N
  have cI := pullbackCompEq_comp_pullbackCompEq b' q' cB rfl hb' hu1 hu1' N
  have u3 := pullbackCompEq_assoc e' ι' cB (ι' ≫ cB) (e' ≫ ι') (j ≫ e ≫ ι) rfl rfl hu3 hu1' N
  have u5 := pullbackCompEq_assoc e' k ι (ι' ≫ cB) (e' ≫ k) (j ≫ e ≫ ι) hι rfl hu3 hu5 N
  have u7 := pullbackCompEq_assoc j e ι (e ≫ ι) (e' ≫ k) (j ≫ e ≫ ι) rfl hk.symm rfl hu5 N
  have v1 := pullbackCompEq_assoc b' yQ q (q' ≫ cB) (b' ≫ yQ) (j ≫ e ≫ ι) hyQ rfl hW hv1 N
  have v3 := pullbackCompEq_assoc j b q (e ≫ ι) (b' ≫ yQ) (j ≫ e ≫ ι) hb hjB rfl hv1 N
  simp only [pullbackCompEq_rfl] at u1 cI u3 u5 u7 v1 v3
  rw [map_inv_hom_app_assoc, u1, cI, Iso.inv_hom_id_app_assoc, ← u3, map_inv_hom_app_assoc, u5,
    Iso.inv_hom_id_app_assoc, ← u7, v1, Iso.inv_hom_id_app_assoc, ← v3, map_inv_hom_app_assoc]


/-- A functor on a composite of nine morphisms. -/
private theorem map_comp₉ {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : 𝒞} (f₁ : x₀ ⟶ x₁) (f₂ : x₁ ⟶ x₂) (f₃ : x₂ ⟶ x₃)
    (f₄ : x₃ ⟶ x₄) (f₅ : x₄ ⟶ x₅) (f₆ : x₅ ⟶ x₆) (f₇ : x₆ ⟶ x₇) (f₈ : x₇ ⟶ x₈) (f₉ : x₈ ⟶ x₉) :
    F.map (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ ≫ f₇ ≫ f₈ ≫ f₉) =
      F.map f₁ ≫ F.map f₂ ≫ F.map f₃ ≫ F.map f₄ ≫ F.map f₅ ≫ F.map f₆ ≫ F.map f₇ ≫ F.map f₈ ≫
        F.map f₉ := by
  simp only [Functor.map_comp]

end Coherence

/-! ### The chart maps of `θ` and of its transport -/

section Transport

open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

variable {S₀ S₀' : Scheme.{u}} {A B : SheafGradedAlgebra S₀} {A' B' : SheafGradedAlgebra S₀'}
  (ψ : SheafGradedAlgebraHom A B) (ψ' : SheafGradedAlgebraHom A' B')
  {cA : (relativeProj A').scheme ⟶ (relativeProj A).scheme}
  {cB : (relativeProj B').scheme ⟶ (relativeProj B).scheme}
  (χA : Stacks.RingedSpace.pullbackGradedAlgebra cA.toLRSHom.toShHom (twistAlgebra A) ≅
    twistAlgebra A')
  (χB : Stacks.RingedSpace.pullbackGradedAlgebra cB.toLRSHom.toShHom (twistAlgebra B) ≅
    twistAlgebra B')
  (k : ψ'.relativeMapDomain.toScheme ⟶ ψ.relativeMapDomain.toScheme)
  (hr : relativeMapHom ψ' ≫ cA = k ≫ relativeMapHom ψ)
  (hι : k ≫ ψ.relativeMapDomain.ι = ψ'.relativeMapDomain.ι ≫ cB)

/-- **`transportTwistHom` in degree `n`**: the nine factors. -/
theorem transportTwistHom_app (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) (n : ℤ) :
    (transportTwistHom ψ ψ' χA χB k hr hι θ).app n =
      ((pullback (relativeMapHom ψ')).map (χA.inv.app n) ≫
        (pullbackComp (relativeMapHom ψ') cA).hom.app ((twistAlgebra A).piece n) ≫
        (pullbackCongr hr).hom.app ((twistAlgebra A).piece n) ≫
        (pullbackComp k (relativeMapHom ψ)).inv.app ((twistAlgebra A).piece n) ≫
        (pullback k).map (θ.app n) ≫
        (pullbackComp k ψ.relativeMapDomain.ι).hom.app ((twistAlgebra B).piece n) ≫
        (pullbackCongr hι).hom.app ((twistAlgebra B).piece n) ≫
        (pullbackComp ψ'.relativeMapDomain.ι cB).inv.app ((twistAlgebra B).piece n) ≫
        (pullback ψ'.relativeMapDomain.ι).map (χB.hom.app n) :
        (pullback (relativeMapHom ψ')).obj ((twistAlgebra A').piece n) ⟶
          (pullback ψ'.relativeMapDomain.ι).obj ((twistAlgebra B').piece n)) :=
  rfl

variable {C P Q C' P' Q' : Scheme.{u}} (a : C ⟶ P) (b : C ⟶ Q)
  (p : P ⟶ (relativeProj A).scheme) (q : Q ⟶ (relativeProj B).scheme)
  (e : C ⟶ ψ.relativeMapDomain.toScheme) (ha : a ≫ p = e ≫ relativeMapHom ψ)
  (hb : b ≫ q = e ≫ ψ.relativeMapDomain.ι) (a' : C' ⟶ P') (b' : C' ⟶ Q')
  (p' : P' ⟶ (relativeProj A').scheme) (q' : Q' ⟶ (relativeProj B').scheme)
  (e' : C' ⟶ ψ'.relativeMapDomain.toScheme) (ha' : a' ≫ p' = e' ≫ relativeMapHom ψ')
  (hb' : b' ≫ q' = e' ≫ ψ'.relativeMapDomain.ι) (j : C' ⟶ C) (yP : P' ⟶ P) (yQ : Q' ⟶ Q)
  (hjA : j ≫ a = a' ≫ yP) (hjB : j ≫ b = b' ≫ yQ) (hyP : yP ≫ p = p' ≫ cA)
  (hyQ : yQ ≫ q = q' ≫ cB)


/-- `chartTwistHom` written out, as a composite of modules on `C`. -/
theorem chartTwistHom_eq (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) (n : ℤ) :
    chartTwistHom ψ a b p q e ha hb θ n =
      ((pullbackComp a p).hom.app ((twistAlgebra A).piece n) ≫
        (pullbackCongr ha).hom.app ((twistAlgebra A).piece n) ≫
        (pullbackComp e (relativeMapHom ψ)).inv.app ((twistAlgebra A).piece n) ≫
        (pullback e).map (X := (pullback (relativeMapHom ψ)).obj ((twistAlgebra A).piece n))
          (Y := (pullback ψ.relativeMapDomain.ι).obj ((twistAlgebra B).piece n)) (θ.app n) ≫
        (pullbackComp e ψ.relativeMapDomain.ι).hom.app ((twistAlgebra B).piece n) ≫
        (pullbackCongr hb).inv.app ((twistAlgebra B).piece n) ≫
        (pullbackComp b q).inv.app ((twistAlgebra B).piece n) :
        (pullback a).obj ((pullback p).obj ((twistAlgebra A).piece n)) ⟶
          (pullback b).obj ((pullback q).obj ((twistAlgebra B).piece n))) :=
  rfl


/-- **The chart map of the transport of `θ` is the pullback of the chart map of `θ`**: for
charts `e : C ⟶ U(ψ)`, `e' : C' ⟶ U(ψ')` and squares `j ≫ a = a' ≫ y_P`, `j ≫ b = b' ≫ y_Q`,
`y_P ≫ p = p' ≫ c_A`, `y_Q ≫ q = q' ≫ c_B`, `e' ≫ k = j ≫ e`, the chart map of
`transportTwistHom θ`, preceded by the comparison of the twists along `y_P` (pulled back along the
square of `j`), is the pullback along `j` of the chart map of `θ`, followed by the comparison of
the twists along `y_Q`. -/
theorem chartTwistHom_transport (hk : e' ≫ k = j ≫ e) (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) (n : ℤ) :
    ((pullbackComp j a).hom.app ((pullback p).obj ((twistAlgebra A).piece n)) ≫
        (pullbackCongr hjA).hom.app ((pullback p).obj ((twistAlgebra A).piece n)) ≫
        (pullbackComp a' yP).inv.app ((pullback p).obj ((twistAlgebra A).piece n)) ≫
        (pullback a').map (AlgebraicGeometry.Space.pullbackIsoOfSquare p p' yP cA hyP
          (AlgebraicGeometry.Space.gradedPieceIso cA χA n)).hom) ≫
        chartTwistHom ψ' a' b' p' q' e' ha' hb' (transportTwistHom ψ ψ' χA χB k hr hι θ) n =
      (pullback j).map (chartTwistHom ψ a b p q e ha hb θ n) ≫
        ((pullbackComp j b).hom.app ((pullback q).obj ((twistAlgebra B).piece n)) ≫
          (pullbackCongr hjB).hom.app ((pullback q).obj ((twistAlgebra B).piece n)) ≫
          (pullbackComp b' yQ).inv.app ((pullback q).obj ((twistAlgebra B).piece n)) ≫
          (pullback b').map (AlgebraicGeometry.Space.pullbackIsoOfSquare q q' yQ cB hyQ
            (AlgebraicGeometry.Space.gradedPieceIso cB χB n)).hom) := by
  have hL := legL j a p a' yP p' cA e (relativeMapHom ψ) e' (relativeMapHom ψ') k ha ha' hr hjA
    hyP hk ((twistAlgebra A).piece n) (AlgebraicGeometry.Space.gradedPieceIso cA χA n)
  have hR := legR j e ψ.relativeMapDomain.ι e' ψ'.relativeMapDomain.ι k cB b q b' q' yQ hb hb' hι
    hjB hyQ hk ((twistAlgebra B).piece n) (AlgebraicGeometry.Space.gradedPieceIso cB χB n)
  have hχA : (AlgebraicGeometry.Space.gradedPieceIso cA χA n).inv = χA.inv.app n := rfl
  have hχB : (AlgebraicGeometry.Space.gradedPieceIso cB χB n).hom = χB.hom.app n := rfl
  rw [hχA] at hL
  rw [hχB] at hR
  have hN : (pullback j).map ((pullback e).map
          (X := (pullback (relativeMapHom ψ)).obj ((twistAlgebra A).piece n))
          (Y := (pullback ψ.relativeMapDomain.ι).obj ((twistAlgebra B).piece n)) (θ.app n)) ≫
      (pullbackComp j e).hom.app ((pullback ψ.relativeMapDomain.ι).obj ((twistAlgebra B).piece n)) ≫
      (pullbackCongr hk.symm).hom.app
        ((pullback ψ.relativeMapDomain.ι).obj ((twistAlgebra B).piece n)) ≫
      (pullbackComp e' k).inv.app
        ((pullback ψ.relativeMapDomain.ι).obj ((twistAlgebra B).piece n)) =
      (pullbackComp j e).hom.app ((pullback (relativeMapHom ψ)).obj ((twistAlgebra A).piece n)) ≫
      (pullbackCongr hk.symm).hom.app
        ((pullback (relativeMapHom ψ)).obj ((twistAlgebra A).piece n)) ≫
      (pullbackComp e' k).inv.app ((pullback (relativeMapHom ψ)).obj ((twistAlgebra A).piece n)) ≫
      (pullback e').map ((pullback k).map
          (X := (pullback (relativeMapHom ψ)).obj ((twistAlgebra A).piece n))
          (Y := (pullback ψ.relativeMapDomain.ι).obj ((twistAlgebra B).piece n)) (θ.app n)) :=
    (pullbackComp j e ≪≫ pullbackCongr hk.symm ≪≫ (pullbackComp e' k).symm).hom.naturality
      (θ.app n)
  have eA : (pullback a').map (AlgebraicGeometry.Space.pullbackIsoOfSquare p p' yP cA hyP
        (AlgebraicGeometry.Space.gradedPieceIso cA χA n)).hom =
      (pullback a').map ((pullbackComp yP p).hom.app ((twistAlgebra A).piece n)) ≫
        (pullback a').map ((pullbackCongr hyP).hom.app ((twistAlgebra A).piece n)) ≫
        (pullback a').map ((pullbackComp p' cA).inv.app ((twistAlgebra A).piece n)) ≫
        (pullback a').map
          ((pullback p').map (AlgebraicGeometry.Space.gradedPieceIso cA χA n).hom) :=
    by simp only [AlgebraicGeometry.Space.pullbackIsoOfSquare, Iso.trans_hom, Functor.map_comp]; rfl
  have eB : (pullback b').map (AlgebraicGeometry.Space.pullbackIsoOfSquare q q' yQ cB hyQ
        (AlgebraicGeometry.Space.gradedPieceIso cB χB n)).hom =
      (pullback b').map ((pullbackComp yQ q).hom.app ((twistAlgebra B).piece n)) ≫
        (pullback b').map ((pullbackCongr hyQ).hom.app ((twistAlgebra B).piece n)) ≫
        (pullback b').map ((pullbackComp q' cB).inv.app ((twistAlgebra B).piece n)) ≫
        (pullback b').map ((pullback q').map (X := (pullback cB).obj ((twistAlgebra B).piece n))
          (Y := (twistAlgebra B').piece n) (χB.hom.app n)) :=
    by simp only [AlgebraicGeometry.Space.pullbackIsoOfSquare, Iso.trans_hom, Functor.map_comp]; rfl
  have eT : (pullback e').map (X := (pullback (relativeMapHom ψ')).obj ((twistAlgebra A').piece n))
        (Y := (pullback ψ'.relativeMapDomain.ι).obj ((twistAlgebra B').piece n))
        ((transportTwistHom ψ ψ' χA χB k hr hι θ).app n) =
      (pullback e').map ((pullback (relativeMapHom ψ')).map (X := (twistAlgebra A').piece n)
          (Y := (pullback cA).obj ((twistAlgebra A).piece n)) (χA.inv.app n)) ≫
        (pullback e').map
          ((pullbackComp (relativeMapHom ψ') cA).hom.app ((twistAlgebra A).piece n)) ≫
        (pullback e').map ((pullbackCongr hr).hom.app ((twistAlgebra A).piece n)) ≫
        (pullback e').map ((pullbackComp k (relativeMapHom ψ)).inv.app ((twistAlgebra A).piece n)) ≫
        (pullback e').map ((pullback k).map
          (X := (pullback (relativeMapHom ψ)).obj ((twistAlgebra A).piece n))
          (Y := (pullback ψ.relativeMapDomain.ι).obj ((twistAlgebra B).piece n)) (θ.app n)) ≫
        (pullback e').map
          ((pullbackComp k ψ.relativeMapDomain.ι).hom.app ((twistAlgebra B).piece n)) ≫
        (pullback e').map ((pullbackCongr hι).hom.app ((twistAlgebra B).piece n)) ≫
        (pullback e').map
          ((pullbackComp ψ'.relativeMapDomain.ι cB).inv.app ((twistAlgebra B).piece n)) ≫
        (pullback e').map ((pullback ψ'.relativeMapDomain.ι).map
          (X := (pullback cB).obj ((twistAlgebra B).piece n)) (Y := (twistAlgebra B').piece n)
          (χB.hom.app n)) :=
    map_comp₉ (pullback e') _ _ _ _ _ _ _ _ _
  have eJ : (pullback j).map (chartTwistHom ψ a b p q e ha hb θ n) =
      (pullback j).map ((pullbackComp a p).hom.app ((twistAlgebra A).piece n)) ≫
        (pullback j).map ((pullbackCongr ha).hom.app ((twistAlgebra A).piece n)) ≫
        (pullback j).map ((pullbackComp e (relativeMapHom ψ)).inv.app ((twistAlgebra A).piece n)) ≫
        (pullback j).map ((pullback e).map
          (X := (pullback (relativeMapHom ψ)).obj ((twistAlgebra A).piece n))
          (Y := (pullback ψ.relativeMapDomain.ι).obj ((twistAlgebra B).piece n)) (θ.app n)) ≫
        (pullback j).map
          ((pullbackComp e ψ.relativeMapDomain.ι).hom.app ((twistAlgebra B).piece n)) ≫
        (pullback j).map ((pullbackCongr hb).inv.app ((twistAlgebra B).piece n)) ≫
        (pullback j).map ((pullbackComp b q).inv.app ((twistAlgebra B).piece n)) :=
    by rw [chartTwistHom_eq ψ]; simp only [Functor.map_comp]
  rw [eA, eB, eJ, chartTwistHom_eq ψ', eT]
  simp only [Category.assoc]
  rw [reassoc_of% hL, ← reassoc_of% hN, hR]

end Transport

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end

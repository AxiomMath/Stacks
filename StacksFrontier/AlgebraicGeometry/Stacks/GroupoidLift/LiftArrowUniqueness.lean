module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SecondOrder

/-!
# Two lifts of a descent arrow differ by an infinitesimal automorphism at the vertex

Let `r` and `r'` be two arrows over the Čech nerve `C' ⊗ C'` from the lifted point `v₀ ∘ u` to
`vₗ ∘ u`, both lifting the descent arrow `rbar` and both satisfying the cocycle condition
exactly. Their quotient `r⁻¹ r'` is an infinitesimal automorphism of the last vertex, a
derivation in the module `N 1` of the décalage
`AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.infDecalage` twisted by `r`. It is a
`1`-cocycle, hence a coboundary (`Stacks.Decalage.Decalage.exists_diff_eq` in degree `0`): an
infinitesimal automorphism `η` of the lifted point `u` over `C'` with `r' = η₀⁻¹ r η₁`, where
`η₀`, `η₁` are its pullbacks to the two vertices.

This is the first-order uniqueness step, one degree below the second-order step
`AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_cocycle_of_lift`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.diff_one_quot`: the quotient is a cocycle.
* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_infH_eq_conj`: two exact cocycle lifts
  of the descent arrow are conjugate by an infinitesimal automorphism at the vertex.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {C' : Type u} [CommRing C'] [Algebra A' C']
  {κ : Cardinal.{u}} {P : Type u} [CommRing P] [Algebra A' P] {G : Groupoid A' κ P}
  {hκ : Cardinal.aleph0 < κ} {hC : Cardinal.mk C' < κ} {I : Ideal A'} {hI : I ^ 2 = ⊥}

/-- In a groupoid, a quotient of two exact cocycles is a cocycle: the word identity behind
`AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.diff_one_quot`. -/
theorem _root_.CategoryTheory.Groupoid.quot_cocycle_word {𝒞 : Type*} [CategoryTheory.Groupoid 𝒞]
    {Y₀ Y₁ Y₂ : 𝒞} {a a' : Y₀ ⟶ Y₁} {b b' : Y₁ ⟶ Y₂} {c c' : Y₀ ⟶ Y₂}
    (h : (CategoryTheory.Groupoid.inv c ≫ a) ≫ b = 𝟙 Y₂)
    (h' : (CategoryTheory.Groupoid.inv c' ≫ a') ≫ b' = 𝟙 Y₂) :
    ((CategoryTheory.Groupoid.inv b ≫ (CategoryTheory.Groupoid.inv a ≫ a')) ≫ b) ≫
        (CategoryTheory.Groupoid.inv b ≫ b') =
      CategoryTheory.Groupoid.inv c ≫ c' := by
  have key : ∀ {x y z : 𝒞} {a : x ⟶ y} {b : y ⟶ z} {c : x ⟶ z},
      (CategoryTheory.Groupoid.inv c ≫ a) ≫ b = 𝟙 z → a ≫ b = c := fun h ↦ by
    rwa [CategoryTheory.Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_comp_eq,
      Category.comp_id] at h
  have e := key h
  have e' := key h'
  subst e e'
  simp

/-- In a groupoid, `η₁ = ((r⁻¹ η₀) r) (r⁻¹ r')` says `r' = η₀⁻¹ r η₁`. -/
theorem _root_.CategoryTheory.Groupoid.eq_conj_of_word {𝒞 : Type*} [CategoryTheory.Groupoid 𝒞]
    {Y₀ Y₁ : 𝒞} {r r' : Y₀ ⟶ Y₁} {η₀ : Y₀ ⟶ Y₀} {η₁ : Y₁ ⟶ Y₁}
    (h : η₁ = ((CategoryTheory.Groupoid.inv r ≫ η₀) ≫ r) ≫ (CategoryTheory.Groupoid.inv r ≫ r')) :
    r' = CategoryTheory.Groupoid.inv η₀ ≫ r ≫ η₁ := by
  subst h
  simp

namespace NerveDatum

variable (D : NerveDatum hκ C' hC I hI G)
  {Q : Type u} [CommRing Q] [Algebra A' Q] {b : Chart G.arr Q} (sV tV : P →ₐ[A'] Q)
  (εbar : Q →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj)
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)
  (hε : b.app _ εbar = G.idt D.ubar) (hb : b.IsFormallyEtale) {u : P →ₐ[A'] C'}
  (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
  {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)} (hrs : G.src r = (v₀ A' C' 1).comp u)
  (hrt : G.tgt r = (vₗ A' C' 1).comp u)
  (hrq : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar)
  {r' : G.arr.obj (nerve (A' := A') hκ C' hC 1)} (hrs' : G.src r' = (v₀ A' C' 1).comp u)
  (hrt' : G.tgt r' = (vₗ A' C' 1).comp u)
  (hrq' : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r' = D.rbar)

omit D in
/-- The cocycle condition makes the defect vanish (the converse of
`AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.cocycle_of_defectH`). -/
theorem defectH_eq_id_of_cocycle {u : P →ₐ[A'] C'} (r' : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hs : G.src r' = (v₀ A' C' 1).comp u) (ht : G.tgt r' = (vₗ A' C' 1).comp u)
    (h' : G.src (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 0)).top r') =
        G.tgt (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 2)).top r'))
    (hcoc : G.comp
          (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 0)).top r')
          (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 2)).top r') h' =
        G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 1)).top r') :
    defectH (I := I) (hI := hI) r' hs ht = 𝟙 _ := by
  unfold defectH
  rw [CategoryTheory.Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_comp_eq, Category.comp_id]
  exact Subtype.ext hcoc

/-! ### The quotient of two lifts reduces to the identity -/

include hrq hrq' in
/-- The quotient `r⁻¹ ≫ r'` of two lifts of the descent arrow `rbar` reduces modulo the
thickening to the identity of the last vertex. -/
theorem map_q_quot :
    G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q
      (CategoryTheory.Groupoid.inv (G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u
          (v₀ A' C' 1)) (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r hrs hrt) ≫
        G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 1))
          (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r' hrs' hrt').1 =
      G.idt (D.wAt (vₗ A' C' 1)) := by
  refine (G.comp_map _ _ _ _).trans ((G.comp_eq' hrq' ((G.inv_map _ r).trans
    (congrArg G.inv hrq)) _ ?_).trans ((G.comp_inv _).trans ?_))
  · exact (G.tgt_inv _).symm
  · exact congrArg G.idt D.tgt_rbar

/-! ### The quotient of two exact lifts is a `1`-cocycle -/

section Cocycle

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] (ε₀ : Q →ₐ[A'] C')
  (hε₀ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp ε₀ = εbar)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `0` to the vertex `1` of level `2`. -/
noncomputable abbrev q01 (r : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hrs : G.src r = (v₀ A' C' 1).comp u) (hrt : G.tgt r = (vₗ A' C' 1).comp u) :
    ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 2) ⟶
      ptAt (G := G) (hκ := hκ) (hC := hC) u ((GroupoidLift.κ A' C' 1).comp (v₀ A' C' 1)) :=
  pullH (I := I) (hI := hI) (m := 2) r hrs hrt (face A' C' 1 2) (AlgHom.ext fun _ ↦ rfl)
    (AlgHom.ext fun _ ↦ rfl)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `1` to the vertex `2` of level `2`. -/
noncomputable abbrev q12 (r : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hrs : G.src r = (v₀ A' C' 1).comp u) (hrt : G.tgt r = (vₗ A' C' 1).comp u) :
    ptAt (G := G) (hκ := hκ) (hC := hC) u ((GroupoidLift.κ A' C' 1).comp (v₀ A' C' 1)) ⟶
      ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 2) :=
  pullH (I := I) (hI := hI) (m := 2) r hrs hrt (face A' C' 1 0) (AlgHom.ext fun _ ↦ rfl)
    (AlgHom.ext fun _ ↦ rfl)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `0` to the vertex `2` of level `2`. -/
noncomputable abbrev q02 (r : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hrs : G.src r = (v₀ A' C' 1).comp u) (hrt : G.tgt r = (vₗ A' C' 1).comp u) :
    ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 2) ⟶
      ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 2) :=
  pullH (I := I) (hI := hI) (m := 2) r hrs hrt (face A' C' 1 1) (AlgHom.ext fun _ ↦ rfl)
    (AlgHom.ext fun _ ↦ rfl)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pullback of the quotient of two arrows along a map of the nerve. -/
theorem mapPt_quot {m : ℕ} (g : cech A' C' 1 →ₐ[A'] cech A' C' m)
    {e e' : C' →ₐ[A'] cech A' C' m} (h₀ : g.comp (v₀ A' C' 1) = e)
    (h₁ : g.comp (vₗ A' C' 1) = e') :
    mapPt (I := I) (hI := hI) g h₁ h₁
        (CategoryTheory.Groupoid.inv (G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u
          (v₀ A' C' 1)) (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r hrs hrt) ≫
          G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 1))
            (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r' hrs' hrt') =
      CategoryTheory.Groupoid.inv (pullH (I := I) (hI := hI) r hrs hrt g h₀ h₁) ≫
        pullH (I := I) (hI := hI) r' hrs' hrt' g h₀ h₁ :=
  (mapPt_comp (I := I) (hI := hI) g h₁ h₀ h₁ _ _).trans
    (congrArg (· ≫ _) (mapPt_inv (I := I) (hI := hI) g h₀ h₁ _))

include hrq hrq' in
/-- **The quotient of two exact lifts of the descent arrow is a `1`-cocycle** of the Čech
complex of infinitesimal automorphisms twisted by the first one. -/
theorem diff_one_quot (hd : defectH (I := I) (hI := hI) r hrs hrt = 𝟙 _)
    (hd' : defectH (I := I) (hI := hI) r' hrs' hrt' = 𝟙 _) (E : N (hI := hI) sV tV εbar 1)
    (hE : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) E.2 =
      CategoryTheory.Groupoid.inv (G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u
          (v₀ A' C' 1)) (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r hrs hrt) ≫
        G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 1))
          (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r' hrs' hrt') :
    (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).diff 1 E = 0 := by
  rw [Stacks.Decalage.Decalage.diff_one_apply]
  have h0 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 1 0 E =
      infFacePlain sV tV εbar 1 0 E :=
    congrArg (· E) (D.infFace_castSucc sV tV εbar hsV htV hε hb hu hrs hrt 1 0)
  have h1 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 1 1 E =
      infFacePlain sV tV εbar 1 1 E :=
    congrArg (· E) (D.infFace_castSucc sV tV εbar hsV htV hε hb hu hrs hrt 1 1)
  have h2 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 1 2 E =
      D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 1 E :=
    congrArg (· E) (D.infFace_last sV tV εbar hsV htV hε hb hu hrs hrt 1)
  rw [h0, h1, h2]
  have hW : ∀ (j : Fin 2) {e : C' →ₐ[A'] cech A' C' 2}
      (h₀ : (face A' C' 1 j.castSucc).comp (v₀ A' C' 1) = e)
      (h₁ : (face A' C' 1 j.castSucc).comp (vₗ A' C' 1) = vₗ A' C' 2),
      D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 2) (infFacePlain sV tV εbar 1 j E).2 =
        CategoryTheory.Groupoid.inv (pullH (I := I) (hI := hI) r hrs hrt _ h₀ h₁) ≫
        pullH (I := I) (hI := hI) r' hrs' hrt' _ h₀ h₁ := fun j _ h₀ h₁ ↦ by
    refine (D.mapPt_infH sV tV εbar hsV htV hε hb hu (face A' C' 1 j.castSucc)
      (vₗ A' C' 1) h₁ E.2 _).symm.trans ?_
    rw [hE]
    exact mapPt_quot hrs hrt hrs' hrt' _ h₀ _
  have hρ : G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u
      ((GroupoidLift.κ A' C' 1).comp (v₀ A' C' 1)))
      (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 2)) (rAt (hI := hI) r 1)
      (src_rAt (I := I) (hI := hI) hrs 1) (tgt_rAt (I := I) (hI := hI) hrt 1) =
        q12 (I := I) (hI := hI) r hrs hrt :=
    Subtype.ext (map_Th_congr (AlgHom.ext fun _ ↦ rfl) r)
  have hW2 : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 2)
      (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 1 E).2 =
      (CategoryTheory.Groupoid.inv (q12 (I := I) (hI := hI) r hrs hrt) ≫
        (CategoryTheory.Groupoid.inv (q01 (I := I) (hI := hI) r hrs hrt) ≫
          q01 (I := I) (hI := hI) r' hrs' hrt')) ≫ q12 (I := I) (hI := hI) r hrs hrt := by
    have h := D.infH_conjK sV tV εbar hsV htV hε hb hu (src_rAt (I := I) (hI := hI) hrs 1)
      (tgt_rAt (I := I) (hI := hI) hrt 1) (postcomp_mem_K2 sV tV _ (hv_last εbar 1) E.2)
    rw [← D.mapPt_infH sV tV εbar hsV htV hε hb hu (face A' C' 1 (Fin.last (1 + 1))) (vₗ A' C' 1)
      (face_last_comp_vₗ 1) E.2, hE] at h
    refine h.trans ?_
    rw [mapPt_quot hrs hrt hrs' hrt' _ (AlgHom.ext fun _ ↦ rfl) (face_last_comp_vₗ 1)]
    exact congrArg (fun t ↦ (CategoryTheory.Groupoid.inv t ≫
      (CategoryTheory.Groupoid.inv (q01 (I := I) (hI := hI) r hrs hrt) ≫
        q01 (I := I) (hI := hI) r' hrs' hrt')) ≫ t) hρ
  have key : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 2)
      (infFacePlain sV tV εbar 1 0 E + D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 1 E).2 =
      D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 2) (infFacePlain sV tV εbar 1 1 E).2 := by
    refine (D.infH_comp sV tV εbar hsV htV hε hb hu _ (infFacePlain sV tV εbar 1 0 E).2
      (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 1 E).2).symm.trans ?_
    rw [hW 0 (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl), hW2,
      hW 1 (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)]
    exact CategoryTheory.Groupoid.quot_cocycle_word hd hd'
  have hsum := Subtype.ext (D.infH_injective sV tV εbar hsV htV hε hb hu _ _ _ key)
  rw [show ∀ x y z : N (hI := hI) sV tV εbar 2, x - z + y = (x + y) - z from
    fun x y z ↦ by abel, hsum, sub_self]

end Cocycle

/-! ### Two exact lifts are conjugate by an infinitesimal automorphism at the vertex -/

section Uniqueness

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.FaithfullyFlat A' C'] (ε₀ : Q →ₐ[A'] C')
  (hε₀ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp ε₀ = εbar)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.FaithfullyFlat A' C'] in
/-- The face map skipping vertex `1` sends the vertex of `C'` to the vertex `0` of `C' ⊗ C'`. -/
theorem face_zero_one_comp_vₗ : (face A' C' 0 1).comp (vₗ A' C' 0) = v₀ A' C' 1 :=
  AlgHom.ext fun _ ↦ rfl

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.FaithfullyFlat A' C'] in
/-- The face map skipping vertex `0` sends the vertex of `C'` to the last vertex of `C' ⊗ C'`. -/
theorem face_zero_zero_comp_vₗ : (face A' C' 0 0).comp (vₗ A' C' 0) = vₗ A' C' 1 :=
  AlgHom.ext fun _ ↦ rfl

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.FaithfullyFlat A' C'] in
/-- At level `1` the lifted descent arrow `rAt r 0` is `r` itself. -/
theorem rAt_zero : rAt (hI := hI) r 0 = r := by
  have h : (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (GroupoidLift.κ A' C' 0)).top = 𝟙 _ :=
    ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl))
  rw [rAt, h, CategoryTheory.Functor.map_id]
  rfl

include sV tV εbar hsV htV hε hb hu hrs hrt hrq hrs' hrt' hrq' ε₀ hε₀ in
/-- **Two exact cocycle lifts of the descent arrow are conjugate by an infinitesimal
automorphism at the vertex.** If `r` and `r'` lift the descent arrow from `v₀ ∘ u` to `vₗ ∘ u`
and both satisfy the cocycle condition exactly, there is an infinitesimal automorphism `η` of
the lifted point `u` over `C'` with `r' = η₀⁻¹ ≫ r ≫ η₁`, where `η₀` and `η₁` are the pullbacks of
`η` to the vertices `0` and `1` of `C' ⊗ C'`. -/
theorem exists_infH_eq_conj (hd : defectH (I := I) (hI := hI) r hrs hrt = 𝟙 _)
    (hd' : defectH (I := I) (hI := hI) r' hrs' hrt' = 𝟙 _) :
    ∃ (E₀ : Q →ₗ[A'] cech A' C' 0)
      (hE₀ : E₀ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC 0)) (vAt εbar (vₗ A' C' 0)) sV tV),
      G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 1))
          (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r' hrs' hrt' =
        CategoryTheory.Groupoid.inv (mapPt (I := I) (hI := hI) (face A' C' 0 1)
            face_zero_one_comp_vₗ face_zero_one_comp_vₗ
            (D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 0) hE₀)) ≫
          G.toHom r hrs hrt ≫ mapPt (I := I) (hI := hI) (face A' C' 0 0)
            face_zero_zero_comp_vₗ face_zero_zero_comp_vₗ
            (D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 0) hE₀) := by
  have hq := D.map_q_quot hrs hrt hrq hrs' hrt' hrq'
  obtain ⟨E, hE, hEq⟩ := D.exists_infAt_eq sV tV εbar hsV htV hε hb hu (vₗ A' C' 1)
    (Groupoid.src_val _ _) (Groupoid.tgt_val _ _) hq
  let x : N (hI := hI) sV tV εbar 1 := ⟨E, hE⟩
  have hx : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) x.2 =
      CategoryTheory.Groupoid.inv (G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u
          (v₀ A' C' 1)) (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r hrs hrt) ≫
        G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 1))
          (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) r' hrs' hrt' :=
    Subtype.ext hEq
  obtain ⟨y, hy⟩ := (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).exists_diff_eq
    0 x (D.diff_one_quot sV tV εbar hsV htV hε hb hu hrs hrt hrq hrs' hrt' hrq' ε₀ hε₀ hd hd' x hx)
  rw [Stacks.Decalage.Decalage.diff_zero_apply] at hy
  have e0 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 0 0 y =
      infFacePlain sV tV εbar 0 0 y :=
    congrArg (· y) (D.infFace_castSucc sV tV εbar hsV htV hε hb hu hrs hrt 0 0)
  have e1 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 0 1 y =
      D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 0 y :=
    congrArg (· y) (D.infFace_last sV tV εbar hsV htV hε hb hu hrs hrt 0)
  rw [e0, e1] at hy
  refine ⟨y.1, y.2, ?_⟩
  have hη₁ : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) (infFacePlain sV tV εbar 0 0 y).2 =
      mapPt (I := I) (hI := hI) (face A' C' 0 0) face_zero_zero_comp_vₗ face_zero_zero_comp_vₗ
        (D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 0) y.2) :=
    (D.mapPt_infH sV tV εbar hsV htV hε hb hu (face A' C' 0 (0 : Fin 1).castSucc) (vₗ A' C' 0)
      face_zero_zero_comp_vₗ y.2 _).symm
  have hc := D.infH_conjK sV tV εbar hsV htV hε hb hu (src_rAt (I := I) (hI := hI) hrs 0)
    (tgt_rAt (I := I) (hI := hI) hrt 0) (postcomp_mem_K2 sV tV _ (hv_last εbar 0) y.2)
  rw [← D.mapPt_infH sV tV εbar hsV htV hε hb hu (face A' C' 0 (Fin.last (0 + 1))) (vₗ A' C' 0)
    (face_last_comp_vₗ 0) y.2] at hc
  have hρ : G.toHom (x := ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 1))
      (y := ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1)) (rAt (hI := hI) r 0)
      (src_rAt (I := I) (hI := hI) hrs 0) (tgt_rAt (I := I) (hI := hI) hrt 0) =
        G.toHom r hrs hrt :=
    Subtype.ext rAt_zero
  have hc' : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1)
      (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 0 y).2 =
      (CategoryTheory.Groupoid.inv (G.toHom r hrs hrt) ≫
        mapPt (I := I) (hI := hI) (face A' C' 0 1) face_zero_one_comp_vₗ face_zero_one_comp_vₗ
          (D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 0) y.2)) ≫ G.toHom r hrs hrt :=
    hc.trans (congrArg (fun t ↦ (CategoryTheory.Groupoid.inv t ≫
      mapPt (I := I) (hI := hI) (face A' C' 0 1) face_zero_one_comp_vₗ face_zero_one_comp_vₗ
          (D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 0) y.2)) ≫ t) hρ)
  have hsum : infFacePlain sV tV εbar 0 0 y =
      x + D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 0 y := by
    rw [← hy]
    abel
  have key : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) (infFacePlain sV tV εbar 0 0 y).2 =
      D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1)
        (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 0 y).2 ≫
        D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) x.2 :=
    (D.infH_congr sV tV εbar hsV htV hε hb hu _ _ (add_mem x.2
      (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 0 y).2)
        (congrArg Subtype.val hsum)).trans
      (D.infH_comp sV tV εbar hsV htV hε hb hu _ x.2
        (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 0 y).2).symm
  rw [hη₁, hc', hx] at key
  exact CategoryTheory.Groupoid.eq_conj_of_word key

end Uniqueness

end NerveDatum

end AlgebraicGeometry.Stack.GroupoidLift

end

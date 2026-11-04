module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.StackOfTorsors.IsomSheaf

/-!
# The presheaf glued from a descent datum of torsors

For a descent datum `D` for `p : 𝒢-Torsors ⥤ C` relative to a covering family with genuine
fibre-product overlaps: the bases of its objects and morphisms, the transitions
`SheafOfGroups.Torsors.Descent.IsTransition` between sections of the `D.x i` over the
overlaps, and the presheaf `SheafOfGroups.Torsors.Descent.gluedPresheaf` on `C/U` of matching
families `SheafOfGroups.Torsors.Descent.Glued`.
-/

/-! ## The glued torsor and effective descent

Condition (3) of Stacks 02ZI is proved below, so all three conditions of Stacks 02ZI are
available and `SheafOfGroups.Torsors.projection_isStackInGroupoids` assembles them.

The construction glues the objects of a descent datum by hand rather than through
Stacks 04TP and 04TS, but it pays the same universe price: the sections of the glued torsor
are matching families indexed by the objects and the morphisms of `C` and by the index set of
the covering family, so the assembled statement is for torsors whose sections lie in
`Type (max u v s t)`, that is, under the bound `max u v s ≤ t`.
-/

@[expose] public section

open CategoryTheory Opposite

universe t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace SheafOfGroups.Torsors

variable {𝒢 : SheafOfGroups.{w} (C := C) J}

universe s

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- The object `D.x i` of a descent datum relative to the covering family `{f i : V i ⟶ U}`
has `V i` as its base. -/
theorem base_x (i : I) : (D.x i).base = V i := D.hx i

/-- The restriction of `D.x i` to the overlap `V i ×_U V j` has that overlap as its base. -/
theorem base_xrij (i j : I) : (D.xrij i j).pt.base = Vij i j := (D.xrij i j).hpt

/-- The restriction of `D.x j` to the overlap `V i ×_U V j` has that overlap as its base. -/
theorem base_xrji (i j : I) : (D.xrji i j).pt.base = Vij i j := (D.xrji i j).hpt

/-- The restriction of `D.x i` to the triple overlap has that overlap as its base. -/
theorem base_wi (i j k : I) : (D.wi i j k).pt.base = Vijk i j k := (D.wi i j k).hpt

/-- The restriction of `D.x j` to the triple overlap has that overlap as its base. -/
theorem base_wj (i j k : I) : (D.wj i j k).pt.base = Vijk i j k := (D.wj i j k).hpt

/-- The restriction of `D.x k` to the triple overlap has that overlap as its base. -/
theorem base_wk (i j k : I) : (D.wk i j k).pt.base = Vijk i j k := (D.wk i j k).hpt

/-- The cartesian morphism `D.x i|_{V i ×_U V j} ⟶ D.x i` lies over the first projection. -/
theorem homBase_xrij (i j : I) : Hom.base (D.xrij i j).hom =
    eqToHom (base_xrij D i j) ≫ pr₁ i j ≫ eqToHom (base_x D i).symm :=
  base_eq_of_isHomLift _ (D.xrij i j).isHomLift

/-- The cartesian morphism `D.x j|_{V i ×_U V j} ⟶ D.x j` lies over the second projection. -/
theorem homBase_xrji (i j : I) : Hom.base (D.xrji i j).hom =
    eqToHom (base_xrji D i j) ≫ pr₂ i j ≫ eqToHom (base_x D j).symm :=
  base_eq_of_isHomLift _ (D.xrji i j).isHomLift

/-- The glueing isomorphism `D.φ i j` is a morphism of the fibre category over the overlap. -/
theorem homBase_phi (i j : I) : Hom.base (D.φ i j) =
    eqToHom (base_xrij D i j) ≫ eqToHom (base_xrji D i j).symm :=
  base_eq_of_isHomLift _ (D.φ_fibreHom i j)

/-- The composite of the glueing isomorphism with the cartesian morphism of `D.x j|_{ij}` lies
over the second projection of the overlap. -/
theorem homBase_glue (i j : I) : Hom.base (D.φ i j ≫ (D.xrji i j).hom) =
    eqToHom (base_xrij D i j) ≫ pr₂ i j ≫ eqToHom (base_x D j).symm := by
  rw [show Hom.base (D.φ i j ≫ (D.xrji i j).hom)
      = Hom.base (D.φ i j) ≫ Hom.base (D.xrji i j).hom from rfl, homBase_phi, homBase_xrji]
  simp

end Descent

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- A morphism `α` of torsors over the same base commuting with two comparison maps `cA`, `cB`
over a common map `s` and with a glueing isomorphism `φ` lying over a self-map of the base
satisfies a commutation relation with `s`. -/
private theorem base_comp_aux {P P' Q Q' : Torsors.{t} 𝒢} {A T : C} (s : T ⟶ A)
    (α : P ⟶ P') (cA : P ⟶ Q) (cB : P' ⟶ Q') (φ : Q ⟶ Q') (h : α ≫ cB = cA ≫ φ)
    (hP : P.base = T) (hP' : P'.base = T) (hQ : Q.base = A) (hQ' : Q'.base = A)
    (hA : Hom.base cA = eqToHom hP ≫ s ≫ eqToHom hQ.symm)
    (hB : Hom.base cB = eqToHom hP' ≫ s ≫ eqToHom hQ'.symm)
    (hφ : Hom.base φ = eqToHom hQ ≫ eqToHom hQ'.symm) :
    Hom.base α ≫ eqToHom hP' ≫ s = eqToHom hP ≫ s := by
  have h' : Hom.base α ≫ Hom.base cB = Hom.base cA ≫ Hom.base φ := congrArg Hom.base h
  rw [hA, hB, hφ] at h'
  simpa using h' =≫ eqToHom hQ'

/-- The glueing isomorphism `D.αij` over the triple overlap lies over a self-map of the triple
overlap which commutes with the projection to the `(i, j)` overlap. -/
theorem homBase_alpha_aux_ij (i j k : I) :
    Hom.base (D.αij i j k) ≫ eqToHom (base_wj D i j k) ≫ s₁₂ i j k =
      eqToHom (base_wi D i j k) ≫ s₁₂ i j k :=
  base_comp_aux _ _ _ _ _ (D.αij_restr i j k) _ _ _ (base_xrji D i j)
    (base_compTo (s₁₂ i j k) (pr₁ i j) (hq₁ i j k) (D.xrij i j) (D.wi i j k)
      (base_xrij D i j) (base_wi D i j k))
    (base_compTo (s₁₂ i j k) (pr₂ i j) (hq₂ i j k) (D.xrji i j) (D.wj i j k)
      (base_xrji D i j) (base_wj D i j k)) (homBase_phi D i j)

/-- The glueing isomorphism `D.αjk` over the triple overlap lies over a self-map of the triple
overlap which commutes with the projection to the `(j, k)` overlap. -/
theorem homBase_alpha_aux_jk (i j k : I) :
    Hom.base (D.αjk i j k) ≫ eqToHom (base_wk D i j k) ≫ s₂₃ i j k =
      eqToHom (base_wj D i j k) ≫ s₂₃ i j k :=
  base_comp_aux _ _ _ _ _ (D.αjk_restr i j k) _ _ _ (base_xrji D j k)
    (base_compTo (s₂₃ i j k) (pr₁ j k) ((hq₂ i j k).trans (hVijk i j k).w) (D.xrij j k)
      (D.wj i j k) (base_xrij D j k) (base_wj D i j k))
    (base_compTo (s₂₃ i j k) (pr₂ j k) (hq₃ i j k) (D.xrji j k) (D.wk i j k)
      (base_xrji D j k) (base_wk D i j k)) (homBase_phi D j k)

/-- The glueing isomorphism `D.αik` over the triple overlap lies over a self-map of the triple
overlap which commutes with the comparison to the `(i, k)` overlap. -/
theorem homBase_alpha_aux_ik (i j k : I) :
    Hom.base (D.αik i j k) ≫ eqToHom (base_wk D i j k) ≫ D.s₁₃ i j k =
      eqToHom (base_wi D i j k) ≫ D.s₁₃ i j k :=
  base_comp_aux _ _ _ _ _ (D.αik_restr i j k) _ _ _ (base_xrji D i k)
    (base_compTo (D.s₁₃ i j k) (pr₁ i k) (D.hs₁₃₁ i j k).symm (D.xrij i k) (D.wi i j k)
      (base_xrij D i k) (base_wi D i j k))
    (base_compTo (D.s₁₃ i j k) (pr₂ i k) (D.hs₁₃₂ i j k).symm (D.xrji i k) (D.wk i j k)
      (base_xrji D i k) (base_wk D i j k)) (homBase_phi D i k)

/-- A self-map `u` of the triple overlap which commutes with the projection to the `(i, j)`
overlap is the identity as soon as it is the first factor of a composite `u ≫ v` commuting with
the comparison to the `(i, k)` overlap, where `v` commutes with the projection to the `(j, k)`
overlap. This is what makes the glueing isomorphisms over the triple overlap of a descent datum
morphisms of the fibre category there. -/
theorem triple_eq_id (i j k : I) (u v : Vijk i j k ⟶ Vijk i j k)
    (hu : u ≫ s₁₂ i j k = s₁₂ i j k) (hv : v ≫ s₂₃ i j k = s₂₃ i j k)
    (hw : (u ≫ v) ≫ D.s₁₃ i j k = D.s₁₃ i j k) : u = 𝟙 (Vijk i j k) := by
  have hvq₃ : v ≫ q₃ i j k = q₃ i j k := by rw [hq₃, ← Category.assoc, hv]
  have huq₃ : u ≫ q₃ i j k = q₃ i j k := by
    have h := hw =≫ pr₂ i k
    rw [Category.assoc, Category.assoc, D.hs₁₃₂, hvq₃] at h
    exact h
  have huq₂ : u ≫ q₂ i j k = q₂ i j k := by rw [hq₂, ← Category.assoc, hu]
  have hu₂₃ : u ≫ s₂₃ i j k = s₂₃ i j k := by
    refine (hVij j k).hom_ext ?_ ?_
    · rw [Category.assoc, ← (hVijk i j k).w, ← Category.assoc, hu]
    · rw [Category.assoc, ← hq₃, huq₃, hq₃]
  refine (hVijk i j k).hom_ext ?_ ?_
  · rw [hu, Category.id_comp]
  · rw [hu₂₃, Category.id_comp]

/-- **The glueing isomorphisms of a descent datum over the triple overlap are morphisms of the
fibre category there.** This is not part of the data of a descent datum, but it follows from the
cocycle condition together with the requirement that each of the three isomorphisms be the
canonical restriction of a glueing isomorphism over a double overlap. -/
theorem homBase_alphaIJ (i j k : I) : Hom.base (D.αij i j k) =
    eqToHom (base_wi D i j k) ≫ eqToHom (base_wj D i j k).symm := by
  have hu : (eqToHom (base_wi D i j k).symm ≫ Hom.base (D.αij i j k) ≫
      eqToHom (base_wj D i j k)) ≫ s₁₂ i j k = s₁₂ i j k := by
    rw [Category.assoc, Category.assoc, homBase_alpha_aux_ij]
    simp
  have hv : (eqToHom (base_wj D i j k).symm ≫ Hom.base (D.αjk i j k) ≫
      eqToHom (base_wk D i j k)) ≫ s₂₃ i j k = s₂₃ i j k := by
    rw [Category.assoc, Category.assoc, homBase_alpha_aux_jk]
    simp
  have hcoc : Hom.base (D.αij i j k) ≫ Hom.base (D.αjk i j k) = Hom.base (D.αik i j k) :=
    (congrArg Hom.base (D.cocycle i j k)).symm
  have hw : ((eqToHom (base_wi D i j k).symm ≫ Hom.base (D.αij i j k) ≫
        eqToHom (base_wj D i j k)) ≫ (eqToHom (base_wj D i j k).symm ≫
        Hom.base (D.αjk i j k) ≫ eqToHom (base_wk D i j k))) ≫ D.s₁₃ i j k =
      D.s₁₃ i j k := by
    have e : (eqToHom (base_wi D i j k).symm ≫ Hom.base (D.αij i j k) ≫
          eqToHom (base_wj D i j k)) ≫ (eqToHom (base_wj D i j k).symm ≫
          Hom.base (D.αjk i j k) ≫ eqToHom (base_wk D i j k)) =
        eqToHom (base_wi D i j k).symm ≫ Hom.base (D.αik i j k) ≫
          eqToHom (base_wk D i j k) := by
      rw [← hcoc]
      simp
    rw [e, Category.assoc, Category.assoc, homBase_alpha_aux_ik]
    simp
  calc Hom.base (D.αij i j k)
      = eqToHom (base_wi D i j k) ≫ (eqToHom (base_wi D i j k).symm ≫
          Hom.base (D.αij i j k) ≫ eqToHom (base_wj D i j k)) ≫
          eqToHom (base_wj D i j k).symm := by simp
    _ = eqToHom (base_wi D i j k) ≫ eqToHom (base_wj D i j k).symm := by
      rw [triple_eq_id D i j k _ _ hu hv hw]
      simp

end Descent

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- The cartesian morphism of the restriction of `D.x i` to the triple overlap lies over the
first of the three projections, written through the `(i, j)` overlap. -/
theorem homBase_wi (i j k : I) : Hom.base (D.wi i j k).hom =
    eqToHom (base_wi D i j k) ≫ (s₁₂ i j k ≫ pr₁ i j) ≫ eqToHom (base_x D i).symm :=
  (base_eq_of_isHomLift _ (D.wi i j k).isHomLift).trans
    (congrArg (fun z => eqToHom (base_wi D i j k) ≫ z ≫ eqToHom (base_x D i).symm)
      (hq₁ i j k))

/-- The composite of `D.αij` with the cartesian morphism of the restriction of `D.x j` to the
triple overlap is the restriction of the glueing isomorphism over the `(i, j)` overlap. -/
theorem compTo_alphaIJ (i j k : I) : D.αij i j k ≫ (D.wj i j k).hom =
    Functor.Restriction.compTo projection (s₁₂ i j k) (pr₁ i j) (hq₁ i j k) (D.xrij i j)
      (D.wi i j k) ≫ (D.φ i j ≫ (D.xrji i j).hom) := by
  rw [← Category.assoc, ← D.αij_restr i j k, Category.assoc,
    Functor.Restriction.compTo_hom]

/-- The composite of `D.αjk` with the cartesian morphism of the restriction of `D.x k` to the
triple overlap is the restriction of the glueing isomorphism over the `(j, k)` overlap. -/
theorem compTo_alphaJK (i j k : I) : D.αjk i j k ≫ (D.wk i j k).hom =
    Functor.Restriction.compTo projection (s₂₃ i j k) (pr₁ j k)
        ((hq₂ i j k).trans (hVijk i j k).w) (D.xrij j k) (D.wj i j k) ≫
      (D.φ j k ≫ (D.xrji j k).hom) := by
  rw [← Category.assoc, ← D.αjk_restr i j k, Category.assoc,
    Functor.Restriction.compTo_hom]

/-- The composite of `D.αik` with the cartesian morphism of the restriction of `D.x k` to the
triple overlap is the restriction of the glueing isomorphism over the `(i, k)` overlap. -/
theorem compTo_alphaIK (i j k : I) : D.αik i j k ≫ (D.wk i j k).hom =
    Functor.Restriction.compTo projection (D.s₁₃ i j k) (pr₁ i k) (D.hs₁₃₁ i j k).symm
      (D.xrij i k) (D.wi i j k) ≫ (D.φ i k ≫ (D.xrji i k).hom) := by
  rw [← Category.assoc, ← D.αik_restr i j k, Category.assoc,
    Functor.Restriction.compTo_hom]

/-- The comparison map between two restrictions of a torsor sends an element lying over `m` to an
element lying over `m ≫ g` with the same image in the torsor. -/
private theorem compTo_map_spec {W V U : C} (g : W ⟶ V) (ff : V ⟶ U) {h : W ⟶ U}
    (hh : h = g ≫ ff) {T : Torsors.{t} 𝒢} {hT : projection.obj T = U}
    (Tr : Functor.Restriction projection ff T hT) (TrW : Functor.Restriction projection h T hT)
    (hTr : Tr.pt.base = V) (hTrW : TrW.pt.base = W) {Z : C} (m : Z ⟶ W)
    (pw : TrW.pt.Total (op Z)) (hpw : pw.1 = m ≫ eqToHom hTrW.symm) :
    ((Functor.Restriction.compTo projection g ff hh Tr TrW).map (op Z) pw).1 =
        (m ≫ g) ≫ eqToHom hTr.symm ∧
      Tr.hom.map (op Z) ((Functor.Restriction.compTo projection g ff hh Tr TrW).map (op Z) pw) =
        TrW.hom.map (op Z) pw := by
  refine ⟨?_, ?_⟩
  · rw [Hom.fst_map, hpw, base_compTo g ff hh Tr TrW hTr hTrW]
    simp
  · rw [show Tr.hom.map (op Z) ((Functor.Restriction.compTo projection g ff hh Tr TrW).map (op Z)
        pw) = (Functor.Restriction.compTo projection g ff hh Tr TrW ≫ Tr.hom).map (op Z) pw
      from rfl, Functor.Restriction.compTo_hom]

/-- **The transition of sections across a glueing isomorphism of a descent datum.** For
`e : Z ⟶ V i ×_U V j`, the element `p` of the total space of `D.x i` over `Z` and the element
`q` of the total space of `D.x j` over `Z` are in transition along `e` when they are the images
of one and the same element of the total space of `D.x i|_{V i ×_U V j}` lying over `e`, under
the cartesian morphism `D.x i|_{ij} ⟶ D.x i` and under its composite with the glueing
isomorphism, `D.x i|_{ij} ⟶ D.x j`. This is the pullback of `D.φ i j` along `e`, recorded as a
relation so that no choice is needed to speak of it. -/
def IsTransition (i j : I) (Z : C) (e : Z ⟶ Vij i j) (p : (D.x i).Total (op Z))
    (q : (D.x j).Total (op Z)) : Prop :=
  ∃ r : (D.xrij i j).pt.Total (op Z), r.1 = e ≫ eqToHom (base_xrij D i j).symm ∧
    (D.xrij i j).hom.map (op Z) r = p ∧ (D.φ i j ≫ (D.xrji i j).hom).map (op Z) r = q

/-- The source of a transition along `e` lies over `e ≫ pr₁ i j`. -/
theorem IsTransition.base_src {i j : I} {Z : C} {e : Z ⟶ Vij i j} {p : (D.x i).Total (op Z)}
    {q : (D.x j).Total (op Z)} (h : IsTransition D i j Z e p q) :
    p.1 = (e ≫ pr₁ i j) ≫ eqToHom (base_x D i).symm := by
  obtain ⟨r, hr₁, hr₂, -⟩ := h
  rw [← hr₂, Hom.fst_map, hr₁, homBase_xrij]
  simp

/-- The target of a transition along `e` lies over `e ≫ pr₂ i j`. -/
theorem IsTransition.base_tgt {i j : I} {Z : C} {e : Z ⟶ Vij i j} {p : (D.x i).Total (op Z)}
    {q : (D.x j).Total (op Z)} (h : IsTransition D i j Z e p q) :
    q.1 = (e ≫ pr₂ i j) ≫ eqToHom (base_x D j).symm := by
  obtain ⟨r, hr₁, -, hr₃⟩ := h
  rw [← hr₃, Hom.fst_map, hr₁, homBase_glue]
  simp

/-- Every element of the total space of `D.x i` lying over `e ≫ pr₁ i j` has a transition
along `e`. -/
theorem exists_isTransition (i j : I) (Z : C) (e : Z ⟶ Vij i j) (p : (D.x i).Total (op Z))
    (hp : p.1 = (e ≫ pr₁ i j) ≫ eqToHom (base_x D i).symm) :
    ∃ q : (D.x j).Total (op Z), IsTransition D i j Z e p q := by
  obtain ⟨r, ⟨hr₁, hr₂⟩, -⟩ := (D.xrij i j).hom.existsUnique_map
    (e ≫ eqToHom (base_xrij D i j).symm) p (by rw [hp, homBase_xrij]; simp)
  exact ⟨(D.φ i j ≫ (D.xrji i j).hom).map (op Z) r, r, hr₁, hr₂, rfl⟩

/-- A transition determines its target. -/
theorem IsTransition.unique {i j : I} {Z : C} {e : Z ⟶ Vij i j} {p : (D.x i).Total (op Z)}
    {q q' : (D.x j).Total (op Z)} (h : IsTransition D i j Z e p q)
    (h' : IsTransition D i j Z e p q') : q = q' := by
  obtain ⟨r, hr₁, hr₂, hr₃⟩ := h
  obtain ⟨r', hr'₁, hr'₂, hr'₃⟩ := h'
  have : r = r' :=
    ((D.xrij i j).hom.bijOn_map (op Z) _).injOn hr₁ hr'₁ (hr₂.trans hr'₂.symm)
  rw [← hr₃, ← hr'₃, this]

/-- A transition determines its source. -/
theorem IsTransition.inj {i j : I} {Z : C} {e : Z ⟶ Vij i j} {p p' : (D.x i).Total (op Z)}
    {q : (D.x j).Total (op Z)} (h : IsTransition D i j Z e p q)
    (h' : IsTransition D i j Z e p' q) : p = p' := by
  obtain ⟨r, hr₁, hr₂, hr₃⟩ := h
  obtain ⟨r', hr'₁, hr'₂, hr'₃⟩ := h'
  have : r = r' :=
    ((D.φ i j ≫ (D.xrji i j).hom).bijOn_map (op Z) _).injOn hr₁ hr'₁ (hr₃.trans hr'₃.symm)
  rw [← hr₂, ← hr'₂, this]

/-- Transitions are compatible with the restriction maps of the total spaces. -/
theorem IsTransition.restrict {i j : I} {Z : C} {e : Z ⟶ Vij i j} {p : (D.x i).Total (op Z)}
    {q : (D.x j).Total (op Z)} (h : IsTransition D i j Z e p q) {Z' : C} (k : Z' ⟶ Z) :
    IsTransition D i j Z' (k ≫ e) ((D.x i).totalMap k.op p) ((D.x j).totalMap k.op q) := by
  obtain ⟨r, hr₁, hr₂, hr₃⟩ := h
  refine ⟨(D.xrij i j).pt.totalMap k.op r, ?_, ?_, ?_⟩
  · rw [totalMap_fst, hr₁]
    simp
  · rw [(D.xrij i j).hom.map_naturality k.op r, hr₂]
  · rw [(D.φ i j ≫ (D.xrji i j).hom).map_naturality k.op r, hr₃]

/-- Transitions are equivariant for the action of `𝒢`. -/
theorem IsTransition.smul {i j : I} {Z : C} {e : Z ⟶ Vij i j} {p : (D.x i).Total (op Z)}
    {q : (D.x j).Total (op Z)} (h : IsTransition D i j Z e p q)
    (γ : 𝒢.presheaf.obj (op Z)) :
    IsTransition D i j Z e ((D.x i).totalSmul γ p) ((D.x j).totalSmul γ q) := by
  obtain ⟨r, hr₁, hr₂, hr₃⟩ := h
  refine ⟨(D.xrij i j).pt.totalSmul γ r, ?_, ?_, ?_⟩
  · rw [totalSmul_fst, hr₁]
  · rw [(D.xrij i j).hom.map_equivariant (op Z) γ r, hr₂]
  · rw [(D.φ i j ≫ (D.xrji i j).hom).map_equivariant (op Z) γ r, hr₃]

/-- **The cocycle condition on transitions.** Two consecutive transitions along the images of a
morphism `m : Z ⟶ V i ×_U V j ×_U V k` into the double overlaps compose to the transition along
its image in the `(i, k)` overlap. This is the one place where the cocycle condition of the
descent datum is used, and the only place where the triple overlaps enter. -/
theorem IsTransition.comp {i j k : I} {Z : C} (m : Z ⟶ Vijk i j k)
    {p : (D.x i).Total (op Z)} {qj : (D.x j).Total (op Z)} {qk : (D.x k).Total (op Z)}
    (h₁ : IsTransition D i j Z (m ≫ s₁₂ i j k) p qj)
    (h₂ : IsTransition D j k Z (m ≫ s₂₃ i j k) qj qk) :
    IsTransition D i k Z (m ≫ D.s₁₃ i j k) p qk := by
  obtain ⟨pw, ⟨hpw₁, hpw₂⟩, -⟩ := (D.wi i j k).hom.existsUnique_map
    (m ≫ eqToHom (base_wi D i j k).symm) p (by
      rw [IsTransition.base_src D h₁, homBase_wi]
      simp)
  obtain ⟨r₁, hr₁₁, hr₁₂, hr₁₃⟩ := h₁
  obtain ⟨r₂, hr₂₁, hr₂₂, hr₂₃⟩ := h₂
  -- the first transition is computed by the comparison into the `(i, j)` overlap
  have hc₁ := compTo_map_spec (s₁₂ i j k) (pr₁ i j) (hq₁ i j k) (D.xrij i j) (D.wi i j k)
    (base_xrij D i j) (base_wi D i j k) m pw hpw₁
  have hr₁eq := ((D.xrij i j).hom.bijOn_map (op Z) _).injOn hr₁₁ hc₁.1
    (hr₁₂.trans (hc₁.2.trans hpw₂).symm)
  have hqj : (D.wj i j k).hom.map (op Z) ((D.αij i j k).map (op Z) pw) = qj := by
    rw [← hr₁₃, hr₁eq]
    exact congrFun (congrFun (congrArg Hom.map (compTo_alphaIJ D i j k)) (op Z)) pw
  -- the second transition is computed by the comparison into the `(j, k)` overlap
  have hpwj : ((D.αij i j k).map (op Z) pw).1 = m ≫ eqToHom (base_wj D i j k).symm := by
    rw [Hom.fst_map, hpw₁, homBase_alphaIJ]
    simp
  have hc₂ := compTo_map_spec (s₂₃ i j k) (pr₁ j k) ((hq₂ i j k).trans (hVijk i j k).w)
    (D.xrij j k) (D.wj i j k) (base_xrij D j k) (base_wj D i j k) m _ hpwj
  have hr₂eq := ((D.xrij j k).hom.bijOn_map (op Z) _).injOn hr₂₁ hc₂.1
    (hr₂₂.trans (hc₂.2.trans hqj).symm)
  -- the composite transition is computed by the comparison into the `(i, k)` overlap
  have hc₃ := compTo_map_spec (D.s₁₃ i j k) (pr₁ i k) (D.hs₁₃₁ i j k).symm (D.xrij i k)
    (D.wi i j k) (base_xrij D i k) (base_wi D i j k) m pw hpw₁
  refine ⟨_, hc₃.1, hc₃.2.trans hpw₂, ?_⟩
  have e₁ := (congrFun (congrFun (congrArg Hom.map (compTo_alphaIK D i j k)) (op Z)) pw).symm
  have e₃ := congrFun (congrFun (congrArg Hom.map (compTo_alphaJK D i j k)) (op Z))
    ((D.αij i j k).map (op Z) pw)
  rw [← hr₂₃, hr₂eq]
  refine e₁.trans (Eq.trans ?_ e₃)
  rw [D.cocycle]
  rfl

/-- **The diagonal transition is trivial.** A transition from `i` to `i` along a morphism into
the overlap `V i ×_U V i` whose two components agree is the identity. This is the consequence of
the cocycle condition at `(i, i, i)` which makes the sections of a glued torsor rigid. -/
theorem IsTransition.diag {i : I} {Z : C} {e : Z ⟶ Vij i i}
    (he : e ≫ pr₁ i i = e ≫ pr₂ i i) {p q : (D.x i).Total (op Z)}
    (h : IsTransition D i i Z e p q) : q = p := by
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : Z ⟶ Vijk i i i, m ≫ s₁₂ i i i = e ∧ m ≫ s₂₃ i i i = e :=
    ⟨(hVijk i i i).lift e e he.symm, (hVijk i i i).lift_fst e e he.symm,
      (hVijk i i i).lift_snd e e he.symm⟩
  have hs₁₃ : m ≫ D.s₁₃ i i i = e := by
    refine (hVij i i).hom_ext ?_ ?_
    · rw [Category.assoc, D.hs₁₃₁, hq₁, ← Category.assoc, hm₁]
    · rw [Category.assoc, D.hs₁₃₂, hq₃, ← Category.assoc, hm₂]
  obtain ⟨q', h'⟩ := exists_isTransition D i i Z e q
    (by rw [IsTransition.base_tgt D h, he])
  have hc : IsTransition D i i Z (m ≫ D.s₁₃ i i i) p q' :=
    IsTransition.comp D m (by rw [hm₁]; exact h) (by rw [hm₂]; exact h')
  rw [hs₁₃] at hc
  have hqq : q' = q := IsTransition.unique D hc h
  rw [hqq] at h'
  exact (IsTransition.inj D h h').symm

end Descent

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- **A section of the sheaf glued from a descent datum.** Over the object `(W, β)` of the
localized site `C/U`, a section of the sheaf glued from `D` is a family assigning to every
factorization `g ≫ β = c ≫ f i` of a morphism `g : Z ⟶ W` of `C` through a member of the
covering family an element of the total space of `D.x i` over `Z` lying over `c`, compatibly
with the restriction maps of the total spaces and with the glueing isomorphisms of `D`. -/
structure Glued {W : C} (β : W ⟶ U) : Type (max u v s t) where
  /-- The element of the total space of `D.x i` attached to a factorization of `g ≫ β`. -/
  sec : ∀ (i : I) (Z : C) (g : Z ⟶ W) (c : Z ⟶ V i), g ≫ β = c ≫ f i → (D.x i).Total (op Z)
  /-- Each attached element lies over the morphism into `V i` of its factorization. -/
  base_sec : ∀ (i : I) (Z : C) (g : Z ⟶ W) (c : Z ⟶ V i) (h : g ≫ β = c ≫ f i),
    (sec i Z g c h).1 = c ≫ eqToHom (base_x D i).symm
  /-- The family is compatible with the restriction maps of the total spaces. -/
  sec_restrict : ∀ (i : I) (Z Z' : C) (k : Z' ⟶ Z) (g : Z ⟶ W) (c : Z ⟶ V i)
    (h : g ≫ β = c ≫ f i) (h' : (k ≫ g) ≫ β = (k ≫ c) ≫ f i),
    (D.x i).totalMap k.op (sec i Z g c h) = sec i Z' (k ≫ g) (k ≫ c) h'
  /-- Over each overlap the two attached elements are in transition along the corresponding
  glueing isomorphism of `D`. -/
  sec_transition : ∀ (i j : I) (Z : C) (g : Z ⟶ W) (e : Z ⟶ Vij i j)
    (h : g ≫ β = (e ≫ pr₁ i j) ≫ f i) (h' : g ≫ β = (e ≫ pr₂ i j) ≫ f j),
    IsTransition D i j Z e (sec i Z g (e ≫ pr₁ i j) h) (sec j Z g (e ≫ pr₂ i j) h')

/-- Two sections of the glued sheaf attaching the same elements to the same factorizations are
equal. -/
theorem Glued.ext' {W : C} {β : W ⟶ U} {G H : Glued D β}
    (h : ∀ (i : I) (Z : C) (g : Z ⟶ W) (c : Z ⟶ V i) (hc : g ≫ β = c ≫ f i),
      G.sec i Z g c hc = H.sec i Z g c hc) : G = H := by
  obtain ⟨s₁, hA₁, hB₁, hC₁⟩ := G
  obtain ⟨s₂, hA₂, hB₂, hC₂⟩ := H
  have hs : s₁ = s₂ := funext fun i => funext fun Z => funext fun g => funext fun c =>
    funext fun hc => h i Z g c hc
  subst hs
  rfl

/-- The element attached by a section of the glued sheaf depends only on the factorization, not
on the proof that it is one. -/
theorem Glued.sec_congr {W : C} {β : W ⟶ U} (G : Glued D β) (i : I) (Z : C)
    {g g' : Z ⟶ W} {c c' : Z ⟶ V i} (hg : g = g') (hc : c = c')
    (h : g ≫ β = c ≫ f i) (h' : g' ≫ β = c' ≫ f i) :
    G.sec i Z g c h = G.sec i Z g' c' h' := by
  subst hg
  subst hc
  rfl

/-- The two elements attached by a section of the glued sheaf to two factorizations of the same
morphism which jointly factor through an overlap are in transition there. -/
theorem Glued.transition {W : C} {β : W ⟶ U} (G : Glued D β) (i j : I) (Z : C) (g : Z ⟶ W)
    {c : Z ⟶ V i} {d : Z ⟶ V j} (e : Z ⟶ Vij i j) (he₁ : e ≫ pr₁ i j = c)
    (he₂ : e ≫ pr₂ i j = d) (h : g ≫ β = c ≫ f i) (h' : g ≫ β = d ≫ f j) :
    IsTransition D i j Z e (G.sec i Z g c h) (G.sec j Z g d h') := by
  subst he₁
  subst he₂
  exact G.sec_transition i j Z g e h h'

/-- The restriction of a section of the glued sheaf along a morphism of `C/U`. -/
def Glued.restrict {W W' : C} {β : W ⟶ U} {β' : W' ⟶ U} (G : Glued D β) (k : W' ⟶ W)
    (hk : k ≫ β = β') : Glued D β' where
  sec i Z g c h := G.sec i Z (g ≫ k) c (by rw [Category.assoc, hk]; exact h)
  base_sec i Z g c h := G.base_sec i Z (g ≫ k) c _
  sec_restrict i Z Z' l g c h h' := by
    have hh : (l ≫ (g ≫ k)) ≫ β = (l ≫ c) ≫ f i := by
      simp only [Category.assoc]
      rw [hk, h]
    refine (G.sec_restrict i Z Z' l (g ≫ k) c _ hh).trans ?_
    exact Glued.sec_congr D G i Z' (Category.assoc l g k).symm rfl _ _
  sec_transition i j Z g e h h' := G.sec_transition i j Z (g ≫ k) e _ _

/-- The element attached by a restricted section of the glued sheaf. -/
theorem Glued.restrict_sec {W W' : C} {β : W ⟶ U} {β' : W' ⟶ U} (G : Glued D β) (k : W' ⟶ W)
    (hk : k ≫ β = β') (i : I) (Z : C) (g : Z ⟶ W') (c : Z ⟶ V i) (h : g ≫ β' = c ≫ f i)
    (h' : (g ≫ k) ≫ β = c ≫ f i) :
    (Glued.restrict D G k hk).sec i Z g c h = G.sec i Z (g ≫ k) c h' :=
  rfl

/-- **The presheaf on `C/U` glued from a descent datum**: its sections over `(W, β)` are the
matching families of `SheafOfGroups.Torsors.Descent.Glued`, and its restriction maps compose
the factorizations with the morphism of `C/U`. -/
def gluedPresheaf : (Over U)ᵒᵖ ⥤ Type (max u v s t) where
  obj Y := Glued D Y.unop.hom
  map k := ↾(fun G => Glued.restrict D G k.unop.left (Over.w k.unop))
  map_id Y := by
    ext G
    exact Glued.ext' D fun i Z g c hc =>
      Glued.sec_congr D G i Z (Category.comp_id g) rfl _ _
  map_comp k l := by
    ext G
    exact Glued.ext' D fun i Z g c hc =>
      Glued.sec_congr D G i Z (Category.assoc g _ _).symm rfl _ _

/-- The element attached by a section of the glued presheaf restricted along a morphism of
`C/U`. -/
theorem gluedPresheaf_map_sec {Y Y' : (Over U)ᵒᵖ} (k : Y ⟶ Y') (G : Glued D Y.unop.hom)
    (i : I) (Z : C) (g : Z ⟶ Y'.unop.left) (c : Z ⟶ V i) (h : g ≫ Y'.unop.hom = c ≫ f i)
    (h' : (g ≫ k.unop.left) ≫ Y.unop.hom = c ≫ f i) :
    ((gluedPresheaf D).map k G).sec i Z g c h = G.sec i Z (g ≫ k.unop.left) c h' :=
  rfl

end Descent

namespace Descent

/-- Two morphisms into the two legs of a pullback square which agree after composition into the
corner factor jointly through the pullback. This is used both for the double overlaps of a
covering family and for its triple overlaps. -/
theorem exists_overlapLift {Z P X Y T : C} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {a : X ⟶ T} {b : Y ⟶ T}
    (hP : IsPullback p₁ p₂ a b) (c : Z ⟶ X) (d : Z ⟶ Y) (h : c ≫ a = d ≫ b) :
    ∃ e : Z ⟶ P, e ≫ p₁ = c ∧ e ≫ p₂ = d :=
  ⟨hP.lift c d h, hP.lift_fst c d h, hP.lift_snd c d h⟩

/-- `exists_overlapLift` for a first leg given as a composite `c ≫ a`. -/
private theorem exists_overlapLift_assoc {Z Z' P X Y T : C} {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    {a : X ⟶ T} {b : Y ⟶ T} (hP : IsPullback p₁ p₂ a b) (g : Z' ⟶ Z) (c : Z ⟶ X) (d : Z' ⟶ Y)
    (h : g ≫ (c ≫ a) = d ≫ b) : ∃ e : Z' ⟶ P, e ≫ p₁ = g ≫ c ∧ e ≫ p₂ = d :=
  exists_overlapLift hP _ _ ((Category.assoc g c a).trans h)

end Descent

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- The comparison from the triple overlap into the `(i, k)` overlap is determined by its two
components. -/
theorem comp_s₁₃_eq (i j k : I) {Z : C} (m : Z ⟶ Vijk i j k) (e : Z ⟶ Vij i k)
    (he₁ : e ≫ pr₁ i k = (m ≫ s₁₂ i j k) ≫ pr₁ i j)
    (he₂ : e ≫ pr₂ i k = (m ≫ s₂₃ i j k) ≫ pr₂ j k) : m ≫ D.s₁₃ i j k = e := by
  refine (hVij i k).hom_ext ?_ ?_
  · rw [Category.assoc, D.hs₁₃₁, hq₁, he₁, Category.assoc]
  · rw [Category.assoc, D.hs₁₃₂, hq₃, he₂, Category.assoc]

/-- **The element attached to an arbitrary factorization by a section of the glued sheaf over
`(Z, c ≫ f i)` is forced**: it is the transition of the restriction of the element attached to
the identity factorization. -/
theorem glued_sec_eq_transition (i j : I) (Z Z' : C) (c : Z ⟶ V i) (G : Glued D (c ≫ f i))
    (g : Z' ⟶ Z) (d : Z' ⟶ V j) (hd : g ≫ (c ≫ f i) = d ≫ f j) (e : Z' ⟶ Vij i j)
    (he₁ : e ≫ pr₁ i j = g ≫ c) (he₂ : e ≫ pr₂ i j = d) :
    IsTransition D i j Z' e
      ((D.x i).totalMap g.op (G.sec i Z (𝟙 Z) c (Category.id_comp _)))
      (G.sec j Z' g d hd) := by
  have h₁ : g ≫ (c ≫ f i) = (g ≫ c) ≫ f i := (Category.assoc g c (f i)).symm
  have h₂ : (g ≫ 𝟙 Z) ≫ (c ≫ f i) = (g ≫ c) ≫ f i := by
    rw [Category.comp_id]
    exact h₁
  have hr : (D.x i).totalMap g.op (G.sec i Z (𝟙 Z) c (Category.id_comp _)) =
      G.sec i Z' g (g ≫ c) h₁ :=
    (G.sec_restrict i Z Z' g (𝟙 Z) c (Category.id_comp _) h₂).trans
      (Glued.sec_congr D G i Z' (Category.comp_id g) rfl h₂ h₁)
  rw [hr]
  exact Glued.transition D G i j Z' g e he₁ he₂ h₁ hd

/-- **The spread of a section of a member of the descent datum.** An element `p` of the total
space of `D.x i` over `Z` lying over `c : Z ⟶ V i` extends to a unique section of the glued
sheaf over `(Z, c ≫ f i)` attaching `p` to the identity factorization. The other attached
elements are the transitions of the restrictions of `p`; that they are compatible over the
overlaps is exactly the cocycle condition of `D`, and that the element attached to the identity
factorization is `p` itself is the cocycle condition at `(i, i, i)`. -/
theorem exists_glued (i : I) (Z : C) (c : Z ⟶ V i) (p : (D.x i).Total (op Z))
    (hp : p.1 = c ≫ eqToHom (base_x D i).symm) :
    ∃! G : Glued D (c ≫ f i), G.sec i Z (𝟙 Z) c (Category.id_comp _) = p := by
  have hmain : ∀ (j : I) (Z' : C) (g : Z' ⟶ Z) (d : Z' ⟶ V j)
      (_ : g ≫ (c ≫ f i) = d ≫ f j),
      ∃ qq : (D.x j).Total (op Z'), ∀ e : Z' ⟶ Vij i j, e ≫ pr₁ i j = g ≫ c →
        e ≫ pr₂ i j = d → IsTransition D i j Z' e ((D.x i).totalMap g.op p) qq := by
    intro j Z' g d h
    obtain ⟨e₀, he₀₁, he₀₂⟩ := exists_overlapLift_assoc (hVij i j) g c d h
    obtain ⟨qq, hqq⟩ := exists_isTransition D i j Z' e₀ ((D.x i).totalMap g.op p)
      (by rw [totalMap_fst, hp, he₀₁]; simp)
    refine ⟨qq, fun e he₁ he₂ => ?_⟩
    have he : e = e₀ := (hVij i j).hom_ext (by rw [he₁, he₀₁]) (by rw [he₂, he₀₂])
    rw [he]
    exact hqq
  choose Sec hSec using hmain
  have hbase : ∀ (j : I) (Z' : C) (g : Z' ⟶ Z) (d : Z' ⟶ V j)
      (h : g ≫ (c ≫ f i) = d ≫ f j),
      (Sec j Z' g d h).1 = d ≫ eqToHom (base_x D j).symm := by
    intro j Z' g d h
    obtain ⟨e, he₁, he₂⟩ := exists_overlapLift_assoc (hVij i j) g c d h
    rw [IsTransition.base_tgt D (hSec j Z' g d h e he₁ he₂), he₂]
  have hrestrict : ∀ (j : I) (Z' Z'' : C) (k : Z'' ⟶ Z') (g : Z' ⟶ Z) (d : Z' ⟶ V j)
      (h : g ≫ (c ≫ f i) = d ≫ f j) (h' : (k ≫ g) ≫ (c ≫ f i) = (k ≫ d) ≫ f j),
      (D.x j).totalMap k.op (Sec j Z' g d h) = Sec j Z'' (k ≫ g) (k ≫ d) h' := by
    intro j Z' Z'' k g d h h'
    obtain ⟨e, he₁, he₂⟩ := exists_overlapLift_assoc (hVij i j) g c d h
    have h₁ : IsTransition D i j Z'' (k ≫ e) ((D.x i).totalMap (k ≫ g).op p)
        ((D.x j).totalMap k.op (Sec j Z' g d h)) := by
      have hres := IsTransition.restrict D (hSec j Z' g d h e he₁ he₂) k
      rwa [(D.x i).totalMap_comp g.op k.op p] at hres
    exact IsTransition.unique D h₁ (hSec j Z'' (k ≫ g) (k ≫ d) h' (k ≫ e)
      (by rw [Category.assoc, he₁, Category.assoc]) (by rw [Category.assoc, he₂]))
  have htrans : ∀ (j k : I) (Z' : C) (g : Z' ⟶ Z) (e' : Z' ⟶ Vij j k)
      (h : g ≫ (c ≫ f i) = (e' ≫ pr₁ j k) ≫ f j)
      (h' : g ≫ (c ≫ f i) = (e' ≫ pr₂ j k) ≫ f k),
      IsTransition D j k Z' e' (Sec j Z' g (e' ≫ pr₁ j k) h)
        (Sec k Z' g (e' ≫ pr₂ j k) h') := by
    intro j k Z' g e' h h'
    obtain ⟨e₁, he₁₁, he₁₂⟩ := exists_overlapLift_assoc (hVij i j) g c (e' ≫ pr₁ j k) h
    obtain ⟨m, hm₁, hm₂⟩ := exists_overlapLift (hVijk i j k) e₁ e' he₁₂
    obtain ⟨qk, hqk⟩ := exists_isTransition D j k Z' e' (Sec j Z' g (e' ≫ pr₁ j k) h)
      (hbase j Z' g (e' ≫ pr₁ j k) h)
    have hcomp : IsTransition D i k Z' (m ≫ D.s₁₃ i j k) ((D.x i).totalMap g.op p) qk :=
      IsTransition.comp D m (by rw [hm₁]; exact hSec j Z' g (e' ≫ pr₁ j k) h e₁ he₁₁ he₁₂)
        (by rw [hm₂]; exact hqk)
    have h₂ := hSec k Z' g (e' ≫ pr₂ j k) h' (m ≫ D.s₁₃ i j k)
      (by rw [Category.assoc, D.hs₁₃₁, hq₁, ← Category.assoc, hm₁, he₁₁])
      (by rw [Category.assoc, D.hs₁₃₂, hq₃, ← Category.assoc, hm₂])
    rw [← IsTransition.unique D hcomp h₂]
    exact hqk
  have hid : Sec i Z (𝟙 Z) c (Category.id_comp _) = p := by
    obtain ⟨e, he₁, he₂⟩ := exists_overlapLift (hVij i i) (𝟙 Z ≫ c) c
      (by rw [Category.id_comp])
    have hT := hSec i Z (𝟙 Z) c (Category.id_comp _) e he₁ he₂
    rw [show (D.x i).totalMap (𝟙 Z).op p = p from (D.x i).totalMap_id p] at hT
    exact IsTransition.diag D (he₁.trans ((Category.id_comp c).trans he₂.symm)) hT
  refine ⟨⟨Sec, hbase, hrestrict, htrans⟩, hid, ?_⟩
  intro H hH
  refine Glued.ext' D fun j Z' g d hd => ?_
  obtain ⟨e, he₁, he₂⟩ := exists_overlapLift_assoc (hVij i j) g c d hd
  have hA := glued_sec_eq_transition D i j Z Z' c H g d hd e he₁ he₂
  rw [hH] at hA
  exact IsTransition.unique D hA (hSec j Z' g d hd e he₁ he₂)

/-- **Two sections in transition spread out to the same section of the glued sheaf.** -/
theorem glued_sec_eq_of_transition (i j : I) (Z : C) (e : Z ⟶ Vij i j)
    (p : (D.x i).Total (op Z)) (q : (D.x j).Total (op Z)) (hpq : IsTransition D i j Z e p q)
    (G : Glued D ((e ≫ pr₁ i j) ≫ f i)) (H : Glued D ((e ≫ pr₂ i j) ≫ f j))
    (hG : G.sec i Z (𝟙 Z) (e ≫ pr₁ i j) (Category.id_comp _) = p)
    (hH : H.sec j Z (𝟙 Z) (e ≫ pr₂ i j) (Category.id_comp _) = q)
    (l : I) (Z' : C) (g : Z' ⟶ Z) (d : Z' ⟶ V l)
    (h₁ : g ≫ ((e ≫ pr₁ i j) ≫ f i) = d ≫ f l)
    (h₂ : g ≫ ((e ≫ pr₂ i j) ≫ f j) = d ≫ f l) :
    G.sec l Z' g d h₁ = H.sec l Z' g d h₂ := by
  obtain ⟨e₁, he₁₁, he₁₂⟩ := exists_overlapLift_assoc (hVij i l) g (e ≫ pr₁ i j) d h₁
  obtain ⟨e₂, he₂₁, he₂₂⟩ := exists_overlapLift_assoc (hVij j l) g (e ≫ pr₂ i j) d h₂
  obtain ⟨m, hm₁, hm₂⟩ := exists_overlapLift (hVijk i j l) (g ≫ e) e₂
    (by rw [Category.assoc, he₂₁])
  have hGt := glued_sec_eq_transition D i l Z Z' (e ≫ pr₁ i j) G g d h₁ e₁ he₁₁ he₁₂
  have hHt := glued_sec_eq_transition D j l Z Z' (e ≫ pr₂ i j) H g d h₂ e₂ he₂₁ he₂₂
  rw [hG] at hGt
  rw [hH] at hHt
  have hcomp : IsTransition D i l Z' (m ≫ D.s₁₃ i j l) ((D.x i).totalMap g.op p)
      (H.sec l Z' g d h₂) :=
    IsTransition.comp D m (by rw [hm₁]; exact IsTransition.restrict D hpq g)
      (by rw [hm₂]; exact hHt)
  have hs : m ≫ D.s₁₃ i j l = e₁ :=
    comp_s₁₃_eq D i j l m e₁ (by rw [he₁₁, hm₁, Category.assoc])
      (by rw [he₁₂, hm₂, he₂₂])
  rw [hs] at hcomp
  exact IsTransition.unique D hGt hcomp

end Descent

end SheafOfGroups.Torsors

end

module

public import StacksFrontier.Algebra.Category.CommAlgCat.CoconeOfRingCocone
public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Flatness of the projection from a cofiltered limit of schemes

Let `D` be a cofiltered diagram of schemes whose transition morphisms are affine and flat, and
let `S' = lim D` be a limit of it. Then every projection `S' ⟶ D i` is flat.

Flatness is local on the target, so the claim may be checked over an affine open `U ⊆ D i`. Its
inverse image in `S'` is the limit of the inverse images of `U` in the schemes `D j` for
`j ⟶ i`, all of them affine, so the ring of functions on that inverse image is the filtered
colimit of the rings of functions on those inverse images, as algebras over `Γ(U)`. Each member
of that filtered system is a flat `Γ(U)`-algebra because the transition morphisms are flat, and
a filtered colimit of flat algebras is flat by the equational criterion for flatness: a relation
in the colimit comes from a relation at a finite stage, where it is trivial, and triviality is
preserved by the colimit maps.

## Main definitions

* `AlgebraicGeometry.opensAlgebraDiagram` — the filtered system of `Γ(U)`-algebras attached to an
  affine open `U` of a stage of the diagram, namely the rings of functions on the inverse images
  of `U` at the later stages.

## Main results

* `AlgebraicGeometry.flat_π_app` — the projection from a cofiltered limit to a stage is flat
  when all transition morphisms are affine and flat.
* `AlgebraicGeometry.flat_π_app_of_essentiallySmall` — the same for an essentially small index
  category whose object and morphism universes are unrelated to the universe of the schemes.

## Implementation notes

The diagram of inverse images of an open subscheme, its limit cone and the limiting property are
those of `AlgebraicGeometry.opensDiagram`, `AlgebraicGeometry.opensCone` and
`AlgebraicGeometry.isLimitOpensCone`; only the passage from schemes to algebras is carried out
here. A cocone of commutative rings under a diagram of algebras is upgraded to a cocone of
algebras by transporting the algebra structure along one leg, which is legitimate because the
index category is filtered, so that any two legs agree after a further transition.

The statement for a general index category is deduced from the statement for a small one by
transporting along the equivalence with a small model, which is again cofiltered.

## References

* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
* [Stacks Project, Tag 05UU](https://stacks.math.columbia.edu/tag/05UU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u a

namespace AlgebraicGeometry

/-! ### Filtered colimits of flat algebras -/

/-- The legs of a cocone of commutative algebras are compatible with the transition maps. -/
private theorem ι_app_map_apply {A : Type u} [CommRing A]
    {J : Type v} [Category.{w} J] {F : J ⥤ CommAlgCat.{a} A} (c : Cocone F)
    {j k : J} (f : j ⟶ k) (a : F.obj j) :
    (c.ι.app k).hom ((F.map f).hom a) = (c.ι.app j).hom a := by
  simp

/-- Every element of the vertex of a colimit cocone of commutative algebras comes from a finite
stage: the elements that do form a subalgebra through which the colimit cocone factors. -/
theorem exists_lift_of_isColimit {A : Type u} [CommRing A]
    {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{a} A} {c : Cocone F} (hc : IsColimit c)
    (x : c.pt) : ∃ (j : J) (y : F.obj j), (c.ι.app j).hom y = x := by
  classical
  let S : Subalgebra A c.pt :=
    { carrier := {x | ∃ (j : J) (y : F.obj j), (c.ι.app j).hom y = x}
      zero_mem' := ⟨IsFiltered.nonempty.some, 0, by simp⟩
      one_mem' := ⟨IsFiltered.nonempty.some, 1, by simp⟩
      add_mem' := by
        rintro x y ⟨j, a, ha⟩ ⟨k, b, hb⟩
        refine ⟨IsFiltered.max j k, (F.map (IsFiltered.leftToMax j k)).hom a +
          (F.map (IsFiltered.rightToMax j k)).hom b, ?_⟩
        simp only [map_add, ι_app_map_apply, ha, hb]
      mul_mem' := by
        rintro x y ⟨j, a, ha⟩ ⟨k, b, hb⟩
        refine ⟨IsFiltered.max j k, (F.map (IsFiltered.leftToMax j k)).hom a *
          (F.map (IsFiltered.rightToMax j k)).hom b, ?_⟩
        simp only [map_mul, ι_app_map_apply, ha, hb]
      algebraMap_mem' := fun r =>
        ⟨IsFiltered.nonempty.some, algebraMap A (F.obj IsFiltered.nonempty.some) r,
          (c.ι.app IsFiltered.nonempty.some).hom.commutes r⟩ }
  let s : Cocone F :=
    { pt := CommAlgCat.of A S
      ι :=
        { app := fun j => CommAlgCat.ofHom <|
            (c.ι.app j).hom.codRestrict S (fun y => ⟨j, y, rfl⟩)
          naturality := by
            intro j k f
            ext y
            exact Subtype.ext (ConcreteCategory.congr_hom (c.w f) y) } }
  let d : c.pt ⟶ s.pt := hc.desc s
  have hid : d ≫ CommAlgCat.ofHom S.val = 𝟙 c.pt := by
    apply hc.hom_ext
    intro j
    ext y
    simp [d, s]
  refine ⟨(d.hom x).property.choose, (d.hom x).property.choose_spec.choose, ?_⟩
  have hx := ConcreteCategory.congr_hom hid x
  change (d.hom x : c.pt) = x at hx
  exact (d.hom x).property.choose_spec.choose_spec.trans hx

/-- A finite family of elements of the vertex of a colimit cocone of commutative algebras comes
from a single finite stage. -/
theorem exists_fin_alg_lift {A : Type u} [CommRing A]
    {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{a} A} {c : Cocone F} (hc : IsColimit c)
    {n : ℕ} (x : Fin n → c.pt) :
    ∃ (j : J) (y : Fin n → F.obj j), ∀ i, (c.ι.app j).hom (y i) = x i := by
  induction n with
  | zero => exact ⟨IsFiltered.nonempty.some, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨j, y, hy⟩ := ih (fun i ↦ x i.castSucc)
      obtain ⟨k, z, hz⟩ := exists_lift_of_isColimit hc (x (Fin.last n))
      refine ⟨IsFiltered.max j k, Fin.lastCases ((F.map (IsFiltered.rightToMax j k)).hom z)
        (fun i ↦ (F.map (IsFiltered.leftToMax j k)).hom (y i)), ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun q ↦ ?_) i
      · simpa [ι_app_map_apply] using hz
      · simpa [ι_app_map_apply] using hy q

/-- A filtered colimit of flat algebras is flat. By the equational criterion it suffices to make
every relation trivial: a relation in the colimit lifts to a finite stage, becomes a relation
after a further transition, is trivial there because that stage is flat, and its witnesses are
carried to the colimit. -/
theorem flat_of_isColimit {A : Type u} [CommRing A]
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{a} A) (c : Cocone F) (hc : IsColimit c)
    (hcD : IsColimit ((forget (CommAlgCat A)).mapCocone c))
    (hF : ∀ j, Module.Flat A (F.obj j)) : Module.Flat A c.pt := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro n f x hx
  obtain ⟨j, y, hy⟩ := exists_fin_alg_lift hc x
  have hsum : (c.ι.app j).hom (∑ i, f i • y i) = 0 := by
    simpa [map_sum, hy] using hx
  obtain ⟨k, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcD
    (∑ i, f i • y i : F.obj j) (0 : F.obj j)).mp (by
      change (c.ι.app j).hom (∑ i, f i • y i) = (c.ι.app j).hom 0
      simpa only [map_zero] using hsum)
  let : Module.Flat A (F.obj k) := hF k
  have hg' : ∑ i, f i • (F.map g).hom (y i) = 0 := by
    change (F.map g).hom (∑ i, f i • y i) = (F.map g).hom 0 at hg
    simpa [map_sum] using hg
  obtain ⟨q, a, z, hza, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hg'
  refine ⟨q, a, fun r ↦ c.ι.app k (z r), ?_, ha⟩
  intro i
  calc
    x i = (c.ι.app j).hom (y i) := (hy i).symm
    _ = (c.ι.app k).hom ((F.map g).hom (y i)) := (ι_app_map_apply c g _).symm
    _ = ∑ r, a i r • (c.ι.app k).hom (z r) := by
      have hza' : (F.map g).hom (y i) = ∑ r, a i r • z r := hza i
      rw [hza']
      simp

/-! ### Algebras of functions on the inverse images of an open subscheme -/

attribute [local simp] Scheme.Hom.resLE_comp_resLE

section Opens

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The structure morphism from the inverse image of `U ⊆ D i` at a later stage to `U`. -/
def opensToBase (i : I) (U : (D.obj i).Opens) (j : Over i) :
    (opensDiagram D i U).obj j ⟶ U.toScheme :=
  (D.map j.hom).resLE U (D.map j.hom ⁻¹ᵁ U) le_rfl

/-- The filtered system of `Γ(U)`-algebras of functions on the inverse images of an open
subscheme `U ⊆ D i` at the later stages. -/
def opensAlgebraDiagram (i : I) (U : (D.obj i).Opens) :
    (Over i)ᵒᵖ ⥤ CommAlgCat.{u} (Γ(U.toScheme, ⊤)) where
  obj j :=
    letI : Algebra (↑Γ(U.toScheme, ⊤)) (↑Γ((opensDiagram D i U).obj j.unop, ⊤)) :=
      RingHom.toAlgebra (opensToBase D i U j.unop).appTop.hom
    CommAlgCat.of (↑Γ(U.toScheme, ⊤)) (↑Γ((opensDiagram D i U).obj j.unop, ⊤))
  map := fun {j k} f ↦ by
    letI : Algebra (↑Γ(U.toScheme, ⊤)) (↑Γ((opensDiagram D i U).obj j.unop, ⊤)) :=
      RingHom.toAlgebra (opensToBase D i U j.unop).appTop.hom
    letI : Algebra (↑Γ(U.toScheme, ⊤)) (↑Γ((opensDiagram D i U).obj k.unop, ⊤)) :=
      RingHom.toAlgebra (opensToBase D i U k.unop).appTop.hom
    refine CommAlgCat.ofHom
      { __ := ((opensDiagram D i U).map f.unop).appTop.hom
        commutes' := ?_ }
    intro r
    have hρ : (opensDiagram D i U).map f.unop ≫ opensToBase D i U j.unop =
        opensToBase D i U k.unop := by
      simp [opensDiagram, opensToBase, Scheme.Hom.resLE_comp_resLE, ← D.map_comp]
    have hh := congrArg (fun φ => φ r)
      (congrArg (fun g : Scheme.Hom _ _ => g.appTop.hom) hρ)
    change ((opensDiagram D i U).map f.unop).appTop.hom
        ((opensToBase D i U j.unop).appTop.hom r) =
      (opensToBase D i U k.unop).appTop.hom r at hh
    simpa [RingHom.algebraMap_toAlgebra'] using hh
  map_id j := by
    let : Algebra (↑Γ(U.toScheme, ⊤)) (↑Γ((opensDiagram D i U).obj j.unop, ⊤)) :=
      RingHom.toAlgebra (opensToBase D i U j.unop).appTop.hom
    ext x
    change ((opensDiagram D i U).map (𝟙 j.unop)).appTop.hom x = x
    rw [(opensDiagram D i U).map_id]
    simp
  map_comp {j k l} f g := by
    let : Algebra (↑Γ(U.toScheme, ⊤)) (↑Γ((opensDiagram D i U).obj j.unop, ⊤)) :=
      RingHom.toAlgebra (opensToBase D i U j.unop).appTop.hom
    let : Algebra (↑Γ(U.toScheme, ⊤)) (↑Γ((opensDiagram D i U).obj l.unop, ⊤)) :=
      RingHom.toAlgebra (opensToBase D i U l.unop).appTop.hom
    ext x
    change ((opensDiagram D i U).map (g.unop ≫ f.unop)).appTop.hom x =
      ((opensDiagram D i U).map g.unop).appTop.hom
        (((opensDiagram D i U).map f.unop).appTop.hom x)
    rw [(opensDiagram D i U).map_comp, Scheme.Hom.comp_appTop]
    rfl

/-- Forgetting the algebra structure of `AlgebraicGeometry.opensAlgebraDiagram` returns the
diagram of rings of functions on the inverse images of `U`. -/
def opensAlgebraDiagramForgetIso (i : I) (U : (D.obj i).Opens) :
    opensAlgebraDiagram D i U ⋙ forget₂ (CommAlgCat.{u} (Γ(U.toScheme, ⊤))) CommRingCat.{u} ≅
      (opensDiagram D i U).op ⋙ Scheme.Γ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro j k f; ext x; rfl)

end Opens

/-! ### Cocones of algebras under a cocone of rings -/

/-- `AlgebraicGeometry.commAlgCoconeOfRingCocone` is a colimit cocone as soon as the cocone of
rings it is built from is one. -/
private def isColimit_commAlgCoconeOfRingCocone
    {A : Type u} [CommRing A] {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{a} A}
    {c : Cocone (F ⋙ forget₂ (CommAlgCat.{a} A) CommRingCat.{a})}
    (hc : IsColimit c) (j : J) :
    IsColimit (Stacks.CommAlgCat.commAlgCoconeOfRingCocone (A := A) c j) where
  desc s := by
    letI : Algebra A c.pt := Stacks.CommAlgCat.algebraOfRingCocone c j
    refine CommAlgCat.ofHom
      { __ := (hc.desc ((forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).mapCocone s)).hom
        commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← ConcreteCategory.comp_apply]
  fac s k := by
    ext
    exact ConcreteCategory.congr_hom (hc.fac ((forget₂ (CommAlgCat.{a} A)
      CommRingCat.{a}).mapCocone s) k) _
  uniq s m hm := by
    ext
    apply ConcreteCategory.congr_hom
      (hc.uniq ((forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).mapCocone s)
        ((forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map m) (fun k ↦ by
          ext x
          exact ConcreteCategory.congr_hom (hm k) x))

/-- Forgetting the algebra structure of a colimit cocone of algebras over a filtered index
category gives a colimit cocone of commutative rings. -/
def isColimit_forgetToCommRing {A : Type u} [CommRing A]
    {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{a} A} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).mapCocone c) where
  desc s := (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map
    (hc.desc (Stacks.CommAlgCat.commAlgCoconeOfRingCocone s IsFiltered.nonempty.some))
  fac s k := by
    change (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map
      (c.ι.app k ≫
        hc.desc (Stacks.CommAlgCat.commAlgCoconeOfRingCocone s IsFiltered.nonempty.some)) = _
    rw [hc.fac]
    rfl
  uniq s m hm := by
    let : Algebra A s.pt := Stacks.CommAlgCat.algebraOfRingCocone s IsFiltered.nonempty.some
    let m' : c.pt ⟶ (Stacks.CommAlgCat.commAlgCoconeOfRingCocone s IsFiltered.nonempty.some).pt :=
      CommAlgCat.ofHom
      { __ := m.hom
        commutes' r := by
          change m.hom (algebraMap A c.pt r) =
            s.ι.app IsFiltered.nonempty.some
              (algebraMap A (F.obj IsFiltered.nonempty.some) r)
          have hh := ConcreteCategory.congr_hom (hm IsFiltered.nonempty.some)
            (algebraMap A (F.obj IsFiltered.nonempty.some) r)
          calc
            m.hom (algebraMap A c.pt r) =
                m.hom ((c.ι.app IsFiltered.nonempty.some).hom
                  (algebraMap A (F.obj IsFiltered.nonempty.some) r)) :=
              congrArg m.hom ((c.ι.app IsFiltered.nonempty.some).hom.commutes r).symm
            _ = s.ι.app IsFiltered.nonempty.some
                  (algebraMap A (F.obj IsFiltered.nonempty.some) r) := by simpa using hh }
    have heq :
        m' = hc.desc (Stacks.CommAlgCat.commAlgCoconeOfRingCocone s IsFiltered.nonempty.some) :=
      hc.uniq _ m' fun k ↦ by
        apply (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map_injective
        change (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map (c.ι.app k) ≫ m = s.ι.app k
        exact hm k
    have hm' : (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map m' = m := by ext x; rfl
    exact hm'.symm.trans (congrArg _ heq)

/-! ### Flatness of the projection -/

/-- A morphism of affine schemes whose map on global sections is flat is flat. -/
private theorem flat_of_appTop_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (hf : f.appTop.hom.Flat) : Flat f := by
  let : MorphismProperty.RespectsIso @Flat := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Flat)]
    exact affineLocally_respectsIso RingHom.Flat RingHom.Flat.propertyIsLocal.respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine f)).mpr
    ((HasRingHomProperty.Spec_iff (P := @Flat)).mpr hf)

section Flat

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The ring of functions on the inverse image of an affine open `U ⊆ D i` in the limit is the
filtered colimit of the rings of functions on the inverse images of `U` at the later stages, as
`Γ(U)`-algebras. -/
private def isColimit_opensAlgebraDiagram (hc : IsLimit c) (i : I) (U : (D.obj i).Opens)
    (hAffine : ∀ j : Over i, IsAffine ((opensDiagram D i U).obj j)) :
    IsColimit (Stacks.CommAlgCat.commAlgCoconeOfRingCocone
      (c := (Cocone.precompose (opensAlgebraDiagramForgetIso D i U).hom).obj
        (Scheme.Γ.mapCocone (opensCone D c i U).op))
      (Opposite.op (Over.mk (𝟙 i)))) := by
  let : ∀ j : (Over i)ᵒᵖ, IsAffine (Opposite.unop ((opensDiagram D i U).op.obj j)) :=
    fun j => hAffine j.unop
  let : PreservesColimit (opensDiagram D i U).op Scheme.Γ :=
    AlgebraicGeometry.preservesColimit_Γ (D := (opensDiagram D i U).op)
  exact isColimit_commAlgCoconeOfRingCocone (A := Γ(U.toScheme, ⊤))
    ((IsColimit.precomposeHomEquiv (opensAlgebraDiagramForgetIso D i U) _).2
      (isColimitOfPreserves Scheme.Γ (isLimitOpensCone D c hc i U).op))
    (Opposite.op (Over.mk (𝟙 i)))

/-- **Flatness of the projection from a cofiltered limit.** If the transition morphisms of a
cofiltered diagram of schemes are affine and flat, then every projection from a limit of the
diagram to a stage of it is flat. -/
theorem flat_π_app (hc : IsLimit c)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f))
    (hFlat : ∀ {i j : I} (f : i ⟶ j), Flat (D.map f)) (i : I) :
    Flat (c.π.app i) := by
  let : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f) := hAffine
  let : ∀ {j k : I} (f : j ⟶ k), Flat (D.map f) := hFlat
  let : IsZariskiLocalAtTarget @Flat := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat)
  let affineCover := (D.obj i).affineCover
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat)
    ((D.obj i).openCoverOfIsOpenCover (fun k => (affineCover.f k).opensRange)
      affineCover.isOpenCover_opensRange)]
  intro k
  let : IsOpenImmersion (affineCover.f k) := affineCover.map_prop k
  let : IsAffine (affineCover.X k) := Scheme.isAffine_affineCover (D.obj i) k
  let U : (D.obj i).Opens := (affineCover.f k).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (affineCover.f k)
  let W : c.pt.Opens := c.π.app i ⁻¹ᵁ U
  have hW : IsAffineOpen W := by
    let : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
    exact hU.preimage (c.π.app i)
  let : IsAffine W.toScheme := hW
  let : IsAffine U.toScheme := hU
  let f : W.toScheme ⟶ U.toScheme := (c.π.app i).resLE U W le_rfl
  let F := opensAlgebraDiagram D i U
  let idx : (Over i)ᵒᵖ := Opposite.op (Over.mk (𝟙 i))
  have hAff : ∀ j : Over i, IsAffine ((opensDiagram D i U).obj j) :=
    fun j ↦ (hAffine j.hom).isAffine_preimage U hU
  have hColim := isColimit_opensAlgebraDiagram D c hc i U hAff
  let cRing := (Cocone.precompose (opensAlgebraDiagramForgetIso D i U).hom).obj
    (Scheme.Γ.mapCocone (opensCone D c i U).op)
  let cAlg := Stacks.CommAlgCat.commAlgCoconeOfRingCocone (c := cRing) idx
  let : Algebra (Γ(U.toScheme, ⊤)) cAlg.pt := Stacks.CommAlgCat.algebraOfRingCocone cRing idx
  have hF : ∀ j : (Over i)ᵒᵖ, Module.Flat (Γ(U.toScheme, ⊤)) (F.obj j) := by
    intro j
    let g := opensToBase D i U j.unop
    let : Flat (D.map j.unop.hom) := hFlat j.unop.hom
    let : Flat g := by
      change Flat ((D.map j.unop.hom).resLE U _ _)
      infer_instance
    exact RingHom.flat_algebraMap_iff.mp (Scheme.Hom.flat_appTop g)
  let : PreservesFilteredColimitsOfSize.{u, u} (forget CommRingCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, u, u} (forget CommRingCat.{u})
  have hAlgFlat : Module.Flat (Γ(U.toScheme, ⊤)) cAlg.pt :=
    flat_of_isColimit F cAlg hColim
      (isColimitOfPreserves (forget CommRingCat) (isColimit_forgetToCommRing hColim)) hF
  have hRingFlat : (algebraMap (Γ(U.toScheme, ⊤)) cAlg.pt).Flat :=
    RingHom.flat_algebraMap_iff.mpr hAlgFlat
  have hTop : f.appTop.hom.Flat := by
    have hcomp : (opensCone D c i U).π.app idx.unop ≫ opensToBase D i U idx.unop = f := by
      change (c.π.app i).resLE _ W _ ≫ (D.map (𝟙 i)).resLE U _ _ = (c.π.app i).resLE U W _
      rw [Scheme.Hom.resLE_comp_resLE]
      simp only [c.w]
    have hfe : f.appTop.hom =
        ((opensCone D c i U).π.app idx.unop ≫ opensToBase D i U idx.unop).appTop.hom :=
      (congrArg (fun g : Scheme.Hom _ _ => g.appTop.hom) hcomp).symm
    rw [hfe]
    exact hRingFlat
  have hFlatRestrict : Flat ((c.π.app i) ∣_ U) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict (f := c.π.app i) (U := U)]
    exact flat_of_appTop_of_isAffine f hTop
  let : Flat ((c.π.app i) ∣_ U) := hFlatRestrict
  have hSnd : Flat (pullback.snd (c.π.app i) U.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  change Flat (pullback.snd (c.π.app i) U.ι)
  exact hSnd

end Flat

/-- **Flatness of the projection from a cofiltered limit**, for an essentially small index
category whose object and morphism universes are unrelated to the universe of the schemes. The
statement is transported from a small model of the index category. -/
theorem flat_π_app_of_essentiallySmall
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f))
    (hFlat : ∀ {i j : I} (f : i ⟶ j), Flat (D.map f)) (i : I) :
    Flat (c.π.app i) := by
  let e := equivSmallModel.{u} I
  have : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence e
  have : Flat (c.π.app (e.inverse.obj (e.functor.obj i))) :=
    flat_π_app (e.inverse ⋙ D) (c.whisker e.inverse) (hc.whiskerEquivalence e.symm)
      (fun f ↦ hAffine (e.inverse.map f)) (fun f ↦ hFlat (e.inverse.map f)) (e.functor.obj i)
  have he : c.π.app (e.inverse.obj (e.functor.obj i)) ≫ D.map (e.unitIso.inv.app i) =
      c.π.app i := c.w (e.unitIso.inv.app i)
  rw [← he]
  infer_instance

end AlgebraicGeometry

end

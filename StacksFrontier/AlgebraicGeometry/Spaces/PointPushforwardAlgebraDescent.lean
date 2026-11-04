module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf

/-!
# Descent of algebra maps into direct images along fppf coverings

Let `X` be an algebraic space, `P` an algebraic space over `X` with representable structure
morphism, and `ι i : Q i ⟶ P` a family of morphisms over `X` from algebraic spaces with
representable structure morphisms.  Suppose that over every étale chart `V` of `X` the
base-changed morphisms `Q i ×_X V ⟶ P ×_X V` generate a covering sieve of the big fppf site.
Then the direct image `P_* 𝒪_P` is the "equalizer" of the direct images `(Q i)_* 𝒪`: a family
of morphisms of `𝒪_X`-algebras `β i : 𝒜 ⟶ (Q i)_* 𝒪` which is compatible on every algebraic
space represented by a scheme mapping to two members of the family factors uniquely through a
morphism `𝒜 ⟶ P_* 𝒪_P`.

This is the descent step behind the sheaf property of the functor of points of a relative
spectrum: for a point `x : T ⟶ X` and an fppf covering of `T`, the base changes of the covering
to the charts `T ×_X V` are again fppf coverings, and global functions are an fppf sheaf.

## Main results

* `AlgebraicGeometry.Space.pushforwardRingMap_app_injective_of_covering` and
  `AlgebraicGeometry.Space.exists_pushforwardRingMap_app_of_covering`: at one étale chart `V`,
  the sections of `P_* 𝒪_P` over `V` are separated and glued by the family of maps to the
  sections of `(Q i)_* 𝒪`.
* `AlgebraicGeometry.Space.existsUnique_pushforwardAlgebra_lift_of_covering`: the resulting
  descent of morphisms of algebra sheaves.

## Implementation notes

At one chart `V` the sections of a direct image are the global functions on the base-changed
chart, by `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, and the map induced by a
morphism over `X` is the pullback of functions along its base change, by
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq`.  Global functions are a sheaf on the big
fppf site, `AlgebraicGeometry.BigFppfSite.isSheaf_globalSections`, so the chart-level statement
is its sheaf condition for the presieve of the base-changed morphisms.  The compatibility of the
family at a test scheme `W` mapping to two base-changed charts is reduced to the compatibility
hypothesis on the algebraic space represented by `W`, using the section `W ⟶ W ×_X V`.

No naturality of `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` in the chart is used:
the morphism of algebra sheaves is assembled chart by chart from the gluing, and its naturality
and its compatibility with the structure maps follow from the separatedness at each chart.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

/-! ### The comparison at one chart, on elements -/

/-- `AlgebraicGeometry.Space.pushforwardRingMap_app_eq` on elements: the chart value of the map
induced by `f : Y ⟶ Z` on direct images is pullback of functions along its base change. -/
theorem pushforwardAlgebraSectionsIso_hom_pushforwardRingMap_app {Y Z : Over X} (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (b : (pushforwardAlgebra B S hS Z).right.obj.obj (op V)) :
    (pushforwardAlgebraSectionsIso B S hS Y hY V).hom
        ((pushforwardRingMap B S hS f).hom.app (op V) b) =
      ((BigFppfOver.toScheme B S hS).map (smallBaseChangeOverMap B S hS f hY hZ V)).appTop
        ((pushforwardAlgebraSectionsIso B S hS Z hZ V).hom b) := by
  have h := ConcreteCategory.congr_hom (pushforwardRingMap_app_eq B S hS f hY hZ V)
    ((pushforwardAlgebraSectionsIso B S hS Z hZ V).hom b)
  simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] at h
  exact h

/-! ### Separation and gluing at one chart -/

section Chart

variable {P : Over X} (hP : yoneda.relativelyRepresentable P.hom.hom)
  {I : Type*} {Q : I → Over X} (hQ : ∀ i, yoneda.relativelyRepresentable (Q i).hom.hom)
  (ι : ∀ i, Q i ⟶ P)

/-- The presieve on the base change `P ×_X V` formed by the base changes `Q i ×_X V ⟶ P ×_X V`
of the family. -/
abbrev chartPresieve (V : SmallEtale B S hS X.1) : Presieve (hP.pullback V.obj.hom) :=
  Presieve.ofArrows (fun i => (hQ i).pullback V.obj.hom)
    (fun i => smallBaseChangeOverMap B S hS (ι i) (hQ i) hP V)

/-- A family of sections of the direct images `(Q i)_* 𝒪` over a chart `V` is *compatible* when
any two members agree after pullback to every algebraic space represented by an object of the
site and mapping to the two corresponding members of the family over `P`. -/
def SectionsCompatible (V : SmallEtale B S hS X.1)
    (b : ∀ i, (pushforwardAlgebra B S hS (Q i)).right.obj.obj (op V)) : Prop :=
  ∀ i j (W : BigFppfOver B S hS) (z : yonedaSpace B S hS W ⟶ X) (p : Over.mk z ⟶ Q i)
    (q : Over.mk z ⟶ Q j), p ≫ ι i = q ≫ ι j →
    (pushforwardRingMap B S hS p).hom.app (op V) (b i) =
      (pushforwardRingMap B S hS q).hom.app (op V) (b j)

/-- The presheaf of global functions on the big fppf site over `S`. -/
abbrev bigFppfGlobalFunctions : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat

/-- A compatible family of sections over a chart gives a compatible family of functions on the
base-changed charts. -/
theorem arrowsCompatible_of_sectionsCompatible (V : SmallEtale B S hS X.1)
    (b : ∀ i, (pushforwardAlgebra B S hS (Q i)).right.obj.obj (op V))
    (hb : SectionsCompatible B S hS ι V b) :
    Presieve.Arrows.Compatible (bigFppfGlobalFunctions B S hS)
      (fun i => smallBaseChangeOverMap B S hS (ι i) (hQ i) hP V)
      (fun i => (pushforwardAlgebraSectionsIso B S hS (Q i) (hQ i) V).hom (b i)) := by
  intro i j W mi mj hm
  have hsnd : mj ≫ (hQ j).snd V.obj.hom = mi ≫ (hQ i).snd V.obj.hom := by
    rw [← smallBaseChangeOverMap_snd B S hS (ι j) (hQ j) hP V, ← Category.assoc, ← hm,
      Category.assoc, smallBaseChangeOverMap_snd]
  have hzj : yoneda.map mj ≫ (hQ j).fst V.obj.hom ≫ (Q j).hom.hom =
      yoneda.map mi ≫ (hQ i).fst V.obj.hom ≫ (Q i).hom.hom := by
    rw [(hQ j).w, (hQ i).w, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, hsnd]
  let zh : yoneda.obj W ⟶ X.1 := yoneda.map mi ≫ (hQ i).fst V.obj.hom ≫ (Q i).hom.hom
  let z : yonedaSpace B S hS W ⟶ X := ObjectProperty.homMk zh
  let mk : ∀ (k : I) (m : W ⟶ (hQ k).pullback V.obj.hom),
      yoneda.map m ≫ (hQ k).fst V.obj.hom ≫ (Q k).hom.hom = zh → (Over.mk z ⟶ Q k) :=
    fun k m h => Over.homMk (ObjectProperty.homMk (yoneda.map m ≫ (hQ k).fst V.obj.hom))
      (ObjectProperty.hom_ext _ ((Category.assoc _ _ _).trans h))
  let p : Over.mk z ⟶ Q i := mk i mi rfl
  let q : Over.mk z ⟶ Q j := mk j mj hzj
  have hpq : p ≫ ι i = q ≫ ι j := by
    refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    show (yoneda.map mi ≫ (hQ i).fst V.obj.hom) ≫ (ι i).left.hom =
      (yoneda.map mj ≫ (hQ j).fst V.obj.hom) ≫ (ι j).left.hom
    rw [Category.assoc, Category.assoc,
      ← yoneda_map_smallBaseChangeOverMap_fst B S hS (ι i) (hQ i) hP V,
      ← yoneda_map_smallBaseChangeOverMap_fst B S hS (ι j) (hQ j) hP V,
      ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hm]
  have hZ : yoneda.relativelyRepresentable (Over.mk z).hom.hom :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS X.2 zh
  have hcond : 𝟙 (yoneda.obj W) ≫ (Over.mk z).hom.hom =
      yoneda.map (mi ≫ (hQ i).snd V.obj.hom) ≫ V.obj.hom := by
    show 𝟙 (yoneda.obj W) ≫ zh = _
    rw [Category.id_comp, Functor.map_comp, Category.assoc, ← (hQ i).w]
  let sec : W ⟶ hZ.pullback V.obj.hom := hZ.lift (𝟙 _) (mi ≫ (hQ i).snd V.obj.hom) hcond
  have hs : ∀ (k : I) (m : W ⟶ (hQ k).pullback V.obj.hom) (h : _),
      m ≫ (hQ k).snd V.obj.hom = mi ≫ (hQ i).snd V.obj.hom →
      sec ≫ smallBaseChangeOverMap B S hS (mk k m h) hZ (hQ k) V = m := fun k m h hms => by
    refine (hQ k).hom_ext ?_ ?_
    · rw [Functor.map_comp, Category.assoc, yoneda_map_smallBaseChangeOverMap_fst,
        ← Category.assoc, hZ.lift_fst, Category.id_comp]
      rfl
    · rw [Category.assoc, smallBaseChangeOverMap_snd, hZ.lift_snd, hms]
  have hsi := hs i mi rfl rfl
  have hsj := hs j mj hzj hsnd
  have key := congrArg (pushforwardAlgebraSectionsIso B S hS (Over.mk z) hZ V).hom
    (hb i j W z p q hpq)
  rw [pushforwardAlgebraSectionsIso_hom_pushforwardRingMap_app B S hS p hZ (hQ i),
    pushforwardAlgebraSectionsIso_hom_pushforwardRingMap_app B S hS q hZ (hQ j)] at key
  show ((BigFppfOver.toScheme B S hS).map mi).appTop _ =
    ((BigFppfOver.toScheme B S hS).map mj).appTop _
  rw [← hsi, ← hsj, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop,
    Scheme.Hom.comp_appTop]
  exact congrArg (fun t => ((BigFppfOver.toScheme B S hS).map sec).appTop t) key

variable (V : SmallEtale B S hS X.1)
  (hcov : Sieve.generate (chartPresieve B S hS hP hQ ι V) ∈
    BigFppfOver.topology B S hS (hP.pullback V.obj.hom))
include hcov

/-- Global functions satisfy the sheaf condition for the presieve of base-changed charts. -/
theorem isSheafFor_chartPresieve :
    (chartPresieve B S hS hP hQ ι V).IsSheafFor (bigFppfGlobalFunctions B S hS) :=
  (Presieve.isSheafFor_iff_generate _).2
    (isSheaf_gammaBigFppfOver B S hS _ hcov)

/-- **Separation at one chart.**  Two sections of `P_* 𝒪_P` over a chart `V` which agree after
pullback to every member of the family are equal. -/
theorem pushforwardRingMap_app_injective_of_covering
    {a a' : (pushforwardAlgebra B S hS P).right.obj.obj (op V)}
    (h : ∀ i, (pushforwardRingMap B S hS (ι i)).hom.app (op V) a =
      (pushforwardRingMap B S hS (ι i)).hom.app (op V) a') :
    a = a' := by
  let e := pushforwardAlgebraSectionsIso B S hS P hP V
  obtain ⟨t, -, ht⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_chartPresieve B S hS hP hQ ι V hcov)
    (fun i => (bigFppfGlobalFunctions B S hS).map
      (smallBaseChangeOverMap B S hS (ι i) (hQ i) hP V).op (e.hom a))
    (fun i j W gi gj hg => by
      have := congrArg (fun k => (bigFppfGlobalFunctions B S hS).map (Quiver.Hom.op k)
        ((pushforwardAlgebraSectionsIso B S hS P hP V).hom a)) hg
      simp only at this
      exact this)
  have h₁ := ht (e.hom a) fun _ => rfl
  have h₂ := ht (e.hom a') fun i => by
    have := congrArg (pushforwardAlgebraSectionsIso B S hS (Q i) (hQ i) V).hom (h i)
    rw [pushforwardAlgebraSectionsIso_hom_pushforwardRingMap_app B S hS (ι i) (hQ i) hP,
      pushforwardAlgebraSectionsIso_hom_pushforwardRingMap_app B S hS (ι i) (hQ i) hP] at this
    exact this.symm
  rw [← Iso.hom_inv_id_apply e a, ← Iso.hom_inv_id_apply e a', h₁, h₂]

/-- **Gluing at one chart.**  A compatible family of sections of the direct images `(Q i)_* 𝒪`
over a chart `V` comes from a section of `P_* 𝒪_P` over `V`. -/
theorem exists_pushforwardRingMap_app_of_covering
    (b : ∀ i, (pushforwardAlgebra B S hS (Q i)).right.obj.obj (op V))
    (hb : SectionsCompatible B S hS ι V b) :
    ∃ a : (pushforwardAlgebra B S hS P).right.obj.obj (op V),
      ∀ i, (pushforwardRingMap B S hS (ι i)).hom.app (op V) a = b i := by
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_chartPresieve B S hS hP hQ ι V hcov) _
    (arrowsCompatible_of_sectionsCompatible B S hS hP hQ ι V b hb)
  let t' : Γ(chartScheme ((smallBaseChange B S hS P.hom hP).obj V), ⊤) := t
  refine ⟨(pushforwardAlgebraSectionsIso B S hS P hP V).inv t', fun i => ?_⟩
  rw [← Iso.hom_inv_id_apply (pushforwardAlgebraSectionsIso B S hS (Q i) (hQ i) V) (b i),
    ← Iso.hom_inv_id_apply (pushforwardAlgebraSectionsIso B S hS (Q i) (hQ i) V)
      ((pushforwardRingMap B S hS (ι i)).hom.app (op V)
        ((pushforwardAlgebraSectionsIso B S hS P hP V).inv t')),
    pushforwardAlgebraSectionsIso_hom_pushforwardRingMap_app B S hS (ι i) (hQ i) hP,
    Iso.inv_hom_id_apply]
  exact congrArg (pushforwardAlgebraSectionsIso B S hS (Q i) (hQ i) V).inv (ht i)

end Chart

/-! ### Descent of morphisms of algebra sheaves -/

section Algebra

variable {P : Over X} (hP : yoneda.relativelyRepresentable P.hom.hom)
  {I : Type*} {Q : I → Over X} (hQ : ∀ i, yoneda.relativelyRepresentable (Q i).hom.hom)
  (ι : ∀ i, Q i ⟶ P)
  (hcov : ∀ V : SmallEtale B S hS X.1, Sieve.generate (chartPresieve B S hS hP hQ ι V) ∈
    BigFppfOver.topology B S hS (hP.pullback V.obj.hom))
  {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (β : ∀ i, A ⟶ pushforwardAlgebra B S hS (Q i))

/-- A family of morphisms of algebra sheaves into the direct images `(Q i)_* 𝒪` is *compatible*
when any two members agree after composing with the direct-image maps of every algebraic space
represented by an object of the site and mapping to the two corresponding members over `P`. -/
def AlgebraMapsCompatible : Prop :=
  ∀ i j (W : BigFppfOver B S hS) (z : yonedaSpace B S hS W ⟶ X) (p : Over.mk z ⟶ Q i)
    (q : Over.mk z ⟶ Q j), p ≫ ι i = q ≫ ι j →
    β i ≫ pushforwardAlgebraMap B S hS p = β j ≫ pushforwardAlgebraMap B S hS q

variable {β}

omit hP hQ in
/-- The sections of a composite with a direct-image map. -/
theorem comp_pushforwardAlgebraMap_app {Q' Q'' : Over X}
    (φ : A ⟶ pushforwardAlgebra B S hS Q') (p : Q'' ⟶ Q')
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : A.right.obj.obj U) :
    (φ ≫ pushforwardAlgebraMap B S hS p).right.hom.app U a =
      (pushforwardRingMap B S hS p).hom.app U (φ.right.hom.app U a) := by
  simp only [AlgebraSheaf.comp_right, pushforwardAlgebraMap_right,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, CommRingCat.comp_apply]

/-- Equal composites with direct-image maps give equal sections after applying the maps. -/
private theorem pushforwardRingMap_app_eq_of_comp_eq {Q₁ Q₂ Q₃ : Over X}
    {φ : A ⟶ pushforwardAlgebra B S hS Q₁} {ψ : A ⟶ pushforwardAlgebra B S hS Q₂}
    {p : Q₃ ⟶ Q₁} {q : Q₃ ⟶ Q₂}
    (h : φ ≫ pushforwardAlgebraMap B S hS p = ψ ≫ pushforwardAlgebraMap B S hS q)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : A.right.obj.obj U) :
    (pushforwardRingMap B S hS p).hom.app U (φ.right.hom.app U a) =
      (pushforwardRingMap B S hS q).hom.app U (ψ.right.hom.app U a) := by
  simpa only [comp_pushforwardAlgebraMap_app] using
    congrArg (fun χ : A ⟶ pushforwardAlgebra B S hS Q₃ => χ.right.hom.app U a) h

omit hP hQ in
/-- For a compatible family of morphisms of algebra sheaves, the images of a section of `𝒜`
under the members of the family form a compatible family of sections. -/
theorem sectionsCompatible_of_algebraMapsCompatible (hβ : AlgebraMapsCompatible B S hS ι β)
    (V : SmallEtale B S hS X.1) (a : A.right.obj.obj (op V)) :
    SectionsCompatible B S hS ι V (fun i => (β i).right.hom.app (op V) a) := by
  intro i j W z p q hpq
  exact pushforwardRingMap_app_eq_of_comp_eq B S hS (hβ i j W z p q hpq) _ a

include hcov

/-- The glued section over a chart. -/
def descApp (hβ : AlgebraMapsCompatible B S hS ι β) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : A.right.obj.obj U) : (pushforwardAlgebra B S hS P).right.obj.obj U :=
  (exists_pushforwardRingMap_app_of_covering B S hS hP hQ ι U.unop (hcov U.unop) _
    (sectionsCompatible_of_algebraMapsCompatible B S hS ι hβ U.unop a)).choose

/-- The glued section restricts along each `ι i` to the image of the section under `β i`. -/
theorem pushforwardRingMap_app_descApp (hβ : AlgebraMapsCompatible B S hS ι β)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : A.right.obj.obj U) (i : I) :
    (pushforwardRingMap B S hS (ι i)).hom.app U (descApp B S hS hP hQ ι hcov hβ U a) =
      (β i).right.hom.app U a :=
  (exists_pushforwardRingMap_app_of_covering B S hS hP hQ ι U.unop (hcov U.unop) _
    (sectionsCompatible_of_algebraMapsCompatible B S hS ι hβ U.unop a)).choose_spec i

/-- Two sections of `P_* 𝒪_P` are equal when their restrictions along every `ι i` agree. -/
theorem descApp_eq_of_forall (U : (SmallEtale B S hS X.1)ᵒᵖ)
    {c c' : (pushforwardAlgebra B S hS P).right.obj.obj U}
    (h : ∀ i, (pushforwardRingMap B S hS (ι i)).hom.app U c =
      (pushforwardRingMap B S hS (ι i)).hom.app U c') : c = c' :=
  pushforwardRingMap_app_injective_of_covering B S hS hP hQ ι U.unop (hcov U.unop) h

/-- The glued section over a chart, as a ring homomorphism. -/
def descRingHom (hβ : AlgebraMapsCompatible B S hS ι β) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    A.right.obj.obj U ⟶ (pushforwardAlgebra B S hS P).right.obj.obj U :=
  CommRingCat.ofHom (R := A.right.obj.obj U) (S := (pushforwardAlgebra B S hS P).right.obj.obj U)
  { toFun := descApp B S hS hP hQ ι hcov hβ U
    map_one' := descApp_eq_of_forall B S hS hP hQ ι hcov U
      fun i => by rw [pushforwardRingMap_app_descApp, map_one, map_one]
    map_mul' a a' := descApp_eq_of_forall B S hS hP hQ ι hcov U
      fun i => by rw [pushforwardRingMap_app_descApp, map_mul, map_mul,
        pushforwardRingMap_app_descApp, pushforwardRingMap_app_descApp]
    map_zero' := descApp_eq_of_forall B S hS hP hQ ι hcov U
      fun i => by rw [pushforwardRingMap_app_descApp, map_zero, map_zero]
    map_add' a a' := descApp_eq_of_forall B S hS hP hQ ι hcov U
      fun i => by rw [pushforwardRingMap_app_descApp, map_add, map_add,
        pushforwardRingMap_app_descApp, pushforwardRingMap_app_descApp] }

/-- The ring homomorphism `descRingHom` sends a section to its glued section `descApp`. -/
theorem descRingHom_apply (hβ : AlgebraMapsCompatible B S hS ι β)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : A.right.obj.obj U) :
    descRingHom B S hS hP hQ ι hcov hβ U a = descApp B S hS hP hQ ι hcov hβ U a :=
  rfl

/-- **Descent of morphisms of algebra sheaves into a direct image.**  A compatible family of
morphisms `𝒜 ⟶ (Q i)_* 𝒪` glues to a morphism `𝒜 ⟶ P_* 𝒪_P`. -/
def descPushforwardAlgebra (hβ : AlgebraMapsCompatible B S hS ι β) :
    A ⟶ pushforwardAlgebra B S hS P where
  right :=
    { hom :=
      { app := descRingHom B S hS hP hQ ι hcov hβ
        naturality := fun U U' f => by
          ext a
          refine descApp_eq_of_forall B S hS hP hQ ι hcov U' fun i => ?_
          have h₁ := ConcreteCategory.congr_hom ((β i).right.hom.naturality f) a
          have h₂ := ConcreteCategory.congr_hom
            ((pushforwardRingMap B S hS (ι i)).hom.naturality f)
            (descApp B S hS hP hQ ι hcov hβ U a)
          simp only [CommRingCat.comp_apply] at h₁ h₂
          simp only [CommRingCat.comp_apply, descRingHom_apply]
          rw [h₂, pushforwardRingMap_app_descApp, pushforwardRingMap_app_descApp]
          exact h₁ } }
  comm U r := descApp_eq_of_forall B S hS hP hQ ι hcov U fun i => by
    change (pushforwardRingMap B S hS (ι i)).hom.app U
        (descApp B S hS hP hQ ι hcov hβ U (A.algebraMap U r)) = _
    rw [pushforwardRingMap_app_descApp, (β i).comm]
    exact ((pushforwardAlgebraMap B S hS (ι i)).comm U r).symm

/-- The descended morphism composed with the direct-image map of `ι i` is `β i`. -/
theorem descPushforwardAlgebra_comp (hβ : AlgebraMapsCompatible B S hS ι β) (i : I) :
    descPushforwardAlgebra B S hS hP hQ ι hcov hβ ≫ pushforwardAlgebraMap B S hS (ι i) =
      β i := by
  refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext ?_)
  refine NatTrans.ext (funext fun U => ?_)
  ext a
  rw [comp_pushforwardAlgebraMap_app]
  exact pushforwardRingMap_app_descApp B S hS hP hQ ι hcov hβ U a i

/-- **Uniqueness of the descended morphism**: morphisms `𝒜 ⟶ P_* 𝒪_P` which agree after
composing with every direct-image map of the family are equal. -/
theorem hom_ext_of_covering {α α' : A ⟶ pushforwardAlgebra B S hS P}
    (h : ∀ i, α ≫ pushforwardAlgebraMap B S hS (ι i) = α' ≫ pushforwardAlgebraMap B S hS (ι i)) :
    α = α' := by
  refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext ?_)
  refine NatTrans.ext (funext fun U => ?_)
  ext a
  refine descApp_eq_of_forall B S hS hP hQ ι hcov U fun i => ?_
  exact pushforwardRingMap_app_eq_of_comp_eq B S hS (h i) U a

/-- **Descent of morphisms of algebra sheaves into a direct image**, as unique existence. -/
theorem existsUnique_pushforwardAlgebra_lift_of_covering
    (hβ : AlgebraMapsCompatible B S hS ι β) :
    ∃! α : A ⟶ pushforwardAlgebra B S hS P,
      ∀ i, α ≫ pushforwardAlgebraMap B S hS (ι i) = β i :=
  ⟨descPushforwardAlgebra B S hS hP hQ ι hcov hβ,
    descPushforwardAlgebra_comp B S hS hP hQ ι hcov hβ,
    fun _α hα => hom_ext_of_covering B S hS hP hQ ι hcov fun i =>
      (hα i).trans (descPushforwardAlgebra_comp B S hS hP hQ ι hcov hβ i).symm⟩

end Algebra

end AlgebraicGeometry.Space

end

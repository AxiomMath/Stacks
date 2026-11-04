module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Quotient

/-!
# Replacing the index category of a cofiltered limit by an essentially small one

Let `D : I ⥤ C` be a diagram whose index category has hom-types in a universe `Type v`
unrelated to `C`, and let `C` be locally `u`-small. Identifying two arrows of `I` whenever `D`
sends them to the same morphism produces a category `Index D` with the same objects, hom-types
that inject into those of `C`, and a factorization `D = proj D ⋙ diagram D`. Then `Index D` is
locally `u`-small unconditionally, it is essentially `u`-small as soon as the *objects* of `I`
are `u`-small, it is cofiltered when `I` is, and a cone over `D` is limiting exactly when the
corresponding cone over `diagram D` is.

For schemes this is the reduction from `D : I ⥤ Scheme.{u}` to an essentially `u`-small
cofiltered diagram, carrying along affine transition morphisms, quasi-compactness and
quasi-separatedness of the stages. The index morphism universe is eliminated outright; the only
residual hypothesis is `Small.{u} I`, which holds when the index objects are taken in `Type u`.

## Main definitions

* `Stacks.LimitIndexReduction.Index`: the index category `I` with arrows identified when `D`
  identifies them, i.e. `CategoryTheory.Quotient D.homRel`.
* `Stacks.LimitIndexReduction.proj` and `Stacks.LimitIndexReduction.diagram`: the two halves of
  the factorization of `D`.
* `Stacks.LimitIndexReduction.diagramCone`: a cone over `D` read as a cone over `diagram D`.

## Main results

* `Stacks.LimitIndexReduction.instLocallySmallIndex`: `Index D` is locally `u`-small, with no
  hypothesis on `I` beyond local `u`-smallness of `C`.
* `Stacks.LimitIndexReduction.instSmallIndex` and
  `Stacks.LimitIndexReduction.instEssentiallySmallIndex`: `Index D` is essentially `u`-small
  when the objects of `I` are `u`-small.
* `Stacks.LimitIndexReduction.essentiallySmall_reduction`: the whole reduction in the hypothesis
  shape of a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
  morphisms.
* `Stacks.LimitIndexReduction.instIsCofilteredIndex`: `Index D` is cofiltered when `I` is.
* `Stacks.LimitIndexReduction.isLimitDiagramCone`: the reduction preserves limit cones.
* `Stacks.LimitIndexReduction.exists_map_eq`: every morphism of `Index D` is sent by
  `diagram D` to a morphism in the image of `D`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u v₁ u₁

namespace Stacks.LimitIndexReduction

section General

variable {C : Type u₁} [Category.{v₁} C] {I : Type w} [Category.{v} I] (D : I ⥤ C)

/-- The index category of `D` with two parallel arrows identified whenever `D` sends them to the
same morphism. Its objects are those of `I`, so it lives in the universe of `I`'s objects. -/
abbrev Index : Type w := CategoryTheory.Quotient D.homRel

/-- The quotient functor onto the reduced index category. -/
abbrev proj : I ⥤ Index D := Quotient.functor D.homRel

/-- `D` read as a diagram on the reduced index category. -/
def diagram : Index D ⥤ C := CategoryTheory.Quotient.lift D.homRel D (by simp)

/-- The reduced diagram `diagram D` is faithful. -/
instance : (diagram D).Faithful :=
  inferInstanceAs (CategoryTheory.Quotient.lift D.homRel D (by simp)).Faithful

/-- `diagram D` sends the image of an object of `I` to its image under `D`. -/
@[simp]
theorem diagram_obj (i : I) : (diagram D).obj ((proj D).obj i) = D.obj i := rfl

/-- `diagram D` sends the image of an arrow of `I` to its image under `D`. -/
@[simp]
theorem diagram_map {i j : I} (f : i ⟶ j) :
    (diagram D).map ((proj D).map f) = D.map f := rfl

/-- Every morphism of the reduced index category is sent by `diagram D` to a morphism in the
image of `D`. -/
theorem exists_map_eq {a b : Index D} (e : a ⟶ b) :
    ∃ f : a.as ⟶ b.as, (diagram D).map e = D.map f := by
  obtain ⟨f, hf⟩ := Quot.exists_rep e
  exact ⟨f, by rw [← hf]; rfl⟩

/-- The reduced index category is `u`-small when the objects of `I` are. -/
instance instSmallIndex [Small.{u} I] : Small.{u} (Index D) :=
  small_of_injective (CategoryTheory.Quotient.equiv D.homRel).injective

/-- The reduced index category is locally `u`-small when `C` is. -/
instance instLocallySmallIndex [LocallySmall.{u} C] : LocallySmall.{u} (Index D) :=
  locallySmall_of_faithful (diagram D)

/-- The reduced index category is essentially `u`-small when `C` is locally `u`-small and the
objects of `I` are `u`-small. -/
instance instEssentiallySmallIndex [LocallySmall.{u} C] [Small.{u} I] :
    EssentiallySmall.{u} (Index D) :=
  essentiallySmall_of_small_of_locallySmall _

/-- The reduced index category is cofiltered when `I` is. -/
instance instIsCofilteredIndex [IsCofiltered I] : IsCofiltered (Index D) where
  nonempty := (IsCofiltered.nonempty : Nonempty I).map fun i => (proj D).obj i
  cone_objs a b := by
    obtain ⟨W, f, g, -⟩ := IsCofilteredOrEmpty.cone_objs a.as b.as
    exact ⟨(proj D).obj W, (proj D).map f, (proj D).map g, trivial⟩
  cone_maps a b e e' := by
    obtain ⟨f, rfl⟩ : ∃ f, (proj D).map f = e := Quot.exists_rep e
    obtain ⟨g, rfl⟩ : ∃ g, (proj D).map g = e' := Quot.exists_rep e'
    obtain ⟨W, h, hh⟩ := IsCofilteredOrEmpty.cone_maps f g
    exact ⟨(proj D).obj W, (proj D).map h, by simp only [← Functor.map_comp, hh]⟩

/-- A cone over `D` read as a cone over the reduced diagram. -/
@[simps pt]
def diagramCone (c : Cone D) : Cone (diagram D) where
  pt := c.pt
  π :=
    { app a := c.π.app a.as
      naturality := by
        rintro ⟨a⟩ ⟨b⟩ e
        obtain ⟨f, rfl⟩ : ∃ f, (proj D).map f = e := Quot.exists_rep e
        exact c.π.naturality f }

/-- The legs of `diagramCone D c` are the legs of `c`. -/
@[simp]
theorem diagramCone_π_app (c : Cone D) (a : Index D) :
    (diagramCone D c).π.app a = c.π.app a.as := rfl

/-- A cone over the reduced diagram read as a cone over `D`. -/
@[simps pt]
def coneOfDiagramCone (t : Cone (diagram D)) : Cone D where
  pt := t.pt
  π :=
    { app i := t.π.app ((proj D).obj i)
      naturality _ _ f := t.π.naturality ((proj D).map f) }

/-- The legs of `coneOfDiagramCone D t` are the legs of `t` at the images of the objects of `I`. -/
@[simp]
theorem coneOfDiagramCone_π_app (t : Cone (diagram D)) (i : I) :
    (coneOfDiagramCone D t).π.app i = t.π.app ((proj D).obj i) := rfl

/-- If `c` is a limit cone over `D`, then `c` read as a cone over the reduced diagram is a limit
cone. -/
def isLimitDiagramCone {c : Cone D} (hc : IsLimit c) : IsLimit (diagramCone D c) where
  lift t := hc.lift (coneOfDiagramCone D t)
  fac t a := hc.fac (coneOfDiagramCone D t) a.as
  uniq t m hm := hc.uniq (coneOfDiagramCone D t) m fun i => hm ((proj D).obj i)

end General

section Schemes

open AlgebraicGeometry

variable {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u})

/-- The stages of the reduced diagram are quasi-compact when those of `D` are. -/
instance instCompactSpaceDiagram [∀ i : I, CompactSpace (D.obj i)] (a : Index D) :
    CompactSpace ((diagram D).obj a) :=
  inferInstanceAs (CompactSpace (D.obj a.as))

/-- The stages of the reduced diagram are quasi-separated when those of `D` are. -/
instance instQuasiSeparatedSpaceDiagram [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (a : Index D) : QuasiSeparatedSpace ((diagram D).obj a) :=
  inferInstanceAs (QuasiSeparatedSpace (D.obj a.as))

/-- The transition morphisms of the reduced diagram are affine when those of `D` are. -/
instance instIsAffineHomDiagram [hD : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    {a b : Index D} (e : a ⟶ b) : IsAffineHom ((diagram D).map e) := by
  obtain ⟨f, hf⟩ := exists_map_eq D e
  exact hf ▸ hD f

/-- Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition morphisms, whose index objects are `u`-small and whose index morphisms live in an
unrelated `Type v`, and let `c` be a limit cone over `D`. Then the reduced index category is
essentially `u`-small and cofiltered, the reduced diagram consists of quasi-compact
quasi-separated schemes with affine transition morphisms, and `c` read as a cone over the reduced
diagram is a limit cone. -/
theorem essentiallySmall_reduction
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [IsCofiltered I] [Small.{u} I] {c : Cone D} (hc : IsLimit c) :
    EssentiallySmall.{u} (Index D) ∧ IsCofiltered (Index D) ∧
      (∀ a : Index D, CompactSpace ((diagram D).obj a)) ∧
      (∀ a : Index D, QuasiSeparatedSpace ((diagram D).obj a)) ∧
      (∀ {a b : Index D} (e : a ⟶ b), IsAffineHom ((diagram D).map e)) ∧
      Nonempty (IsLimit (diagramCone D c)) :=
  ⟨inferInstance, inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, ⟨isLimitDiagramCone D hc⟩⟩

/-- When the index objects lie in the universe `Type u` of the schemes, the reduced index
category of a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms is essentially `u`-small and cofiltered, and a limit cone over `D` read as a cone over
the reduced diagram is a limit cone. -/
theorem essentiallySmall_reduction_of_small_objects
    {I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [IsCofiltered I] {c : Cone D} (hc : IsLimit c) :
    EssentiallySmall.{u} (Index D) ∧ IsCofiltered (Index D) ∧
      Nonempty (IsLimit (diagramCone D c)) :=
  ⟨inferInstance, inferInstance, ⟨isLimitDiagramCone D hc⟩⟩

end Schemes

end Stacks.LimitIndexReduction

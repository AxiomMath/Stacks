module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts

/-!
# Descent objects and their pushforward

For an object `x` of a category cofibered in groupoids over `𝒞_Λ`, the descent category of `x`
consists of the arrows into `x` whose base map is injective, that is, of the subalgebras of
`p(x)` over which `x` descends. A descent object is minimal when every morphism into it is an
isomorphism. A morphism `g : y ⟶ x` induces a functor on descent categories: one takes the
image of the subalgebra under the base map of `g` and pushes the object forward to it.

This is the construction that precedes the descent half of Stacks 90.14 on minimal versal
formal objects; it carries no tag of its own.

## Main definitions

* `Deformation.DescentObject`: the full subcategory of `Over x` consisting of the arrows whose
  base maps are injective.
* `Deformation.IsMinimalObject`: every incoming morphism is an isomorphism.
* `Deformation.DescentPushforward`: the pushforward functor together with its natural
  cocartesian comparison arrows and its image subalgebras.
* `Deformation.descentPushforward`: the construction of this specified pushforward.

## Main results

* `Deformation.ArtinianLocalAlgCat.epi_of_surjective` and
  `Deformation.ArtinianLocalAlgCat.mono_of_injective`: surjective and injective morphisms of
  `𝒞_Λ` are epimorphisms and monomorphisms.
* `Deformation.ArtinianLocalAlgCat.exists_factor_of_range_le`: a morphism factors through an
  injective morphism whose range contains its own.
* `Deformation.epi_of_epi_map`: in a category cofibered in groupoids, a morphism whose image
  is an epimorphism is an epimorphism.

## Implementation notes

A subalgebra is represented invariantly by an injective morphism of `𝒞_Λ`. The full-subcategory
and over-category APIs then give the objects, morphisms, composition and isomorphisms of the
descent category directly: `X.obj.hom` is its arrow to `x`, and `f.hom.left` is the underlying
morphism of a morphism of descent objects.

In `DescentPushforward`, the range equality identifies the output subalgebra with the image of
the input subalgebra under the base map. Together with the commuting square and injectivity of
the output inclusion, it identifies the base map of the comparison arrow with the surjection
onto that image. Strong cocartesianness specifies the pushforward universal property,
including the uniqueness of the resulting arrow to `x`, and naturality specifies the induced
maps of descent objects. So the construction comes with its full specification, independently
of any choice of representatives of subalgebras; its projections can be used in dependent
types, while minimality and the descent category use the APIs of their displayed expansions.

`IsMinimalObject` is named so as not to clash with `Deformation.GroupoidInFunctors.IsMinimal`
of Stacks 06KM, which is minimality of a groupoid in functors rather than of an object.

## References

* [Stacks Project, Tag 06T1](https://stacks.math.columbia.edu/tag/06T1)
-/

@[expose] public section

open CategoryTheory

universe u v w u₁ v₁

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type u₁} [Category.{v₁} F]

/-- The descent category of `x`: arrows to `x` lying over subalgebra inclusions,
with all morphisms over `x`. -/
abbrev DescentObject (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (x : F) :=
  ObjectProperty.FullSubcategory
    (fun X : Over x ↦ Function.Injective (p.map X.hom).hom)

/-- An object is minimal if every morphism into it is an isomorphism. Applied
to `DescentObject p x`, this is minimality of a descent of `x`. -/
abbrev IsMinimalObject {C : Type*} [Category* C] (X : C) : Prop :=
  ∀ (Y : C) (f : Y ⟶ X), IsIso f

/-- Pushforward of descent objects along `g : y ⟶ x`, specified by taking
images of subalgebras and the corresponding natural cocartesian arrows. -/
structure DescentPushforward
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) {y x : F} (g : y ⟶ x) where
  /-- The functor on descent categories. -/
  functor : DescentObject p y ⥤ DescentObject p x
  /-- The arrow from each descent object to its pushforward. -/
  inclusion : ∀ X, X.obj.left ⟶ (functor.obj X).obj.left
  /-- Each comparison arrow is a cocartesian pushforward over its base map. -/
  inclusion_cocartesian : ∀ X,
    p.IsStronglyCocartesian (p.map (inclusion X)) (inclusion X)
  /-- The pushforward square commutes. -/
  inclusion_fac : ∀ X,
    inclusion X ≫ (functor.obj X).obj.hom = X.obj.hom ≫ g
  /-- The output subalgebra is exactly the image of the input subalgebra
  under the base map of `g`. -/
  base_range : ∀ X,
    AlgHom.range (p.map (functor.obj X).obj.hom).hom =
      AlgHom.range (p.map (X.obj.hom ≫ g)).hom
  /-- The comparison arrows are natural in morphisms over `y`. -/
  inclusion_naturality : ∀ {X Y} (f : X ⟶ Y),
    inclusion X ≫ (functor.map f).hom.left = f.hom.left ≫ inclusion Y

/-- The image inherits its Artinian local structure and residue-field identification
from the source, so the usual image factorization stays in the base category. -/
private theorem image_factorization {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ B) :
    ∃ (I : ArtinianLocalAlgCat.{u, v, w} Λ k) (q : A ⟶ I) (j : I ⟶ B),
      q ≫ j = f ∧ Function.Surjective q.hom ∧ Function.Injective j.hom ∧
        AlgHom.range j.hom = AlgHom.range f.hom := by
  let R := f.hom.range
  let q := f.hom.rangeRestrict
  have hq : Function.Surjective q := f.hom.rangeRestrict_surjective
  let : IsArtinianRing R := hq.isArtinianRing
  let : IsLocalRing R := IsLocalRing.of_surjective' q.toRingHom hq
  let : IsLocalHom q := ⟨fun a ha ↦
    isUnit_of_map_unit f.hom a (ha.map R.val)⟩
  let e : IsLocalRing.ResidueField A ≃ₐ[Λ] IsLocalRing.ResidueField R :=
    AlgEquiv.ofBijective (IsLocalRing.ResidueField.mapAlgHom q)
      ⟨(IsLocalRing.ResidueField.mapAlgHom q).toRingHom.injective, by
        intro z
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
        obtain ⟨a, rfl⟩ := hq r
        exact ⟨IsLocalRing.residue A a, rfl⟩⟩
  let I : ArtinianLocalAlgCat.{u, v, w} Λ k :=
    { carrier := R
      residueEquiv := e.symm.trans A.residueEquiv }
  have he (a : A) :
      I.residueEquiv (IsLocalRing.residue I (q a)) =
        A.residueEquiv (IsLocalRing.residue A a) :=
    congrArg A.residueEquiv (e.symm_apply_apply (IsLocalRing.residue A a))
  let q' : A ⟶ I := ⟨q, ⟨fun a ha ↦ isUnit_of_map_unit q a ha⟩, he⟩
  let j : I ⟶ B :=
    { hom := R.val
      isLocal := ⟨fun r hr ↦ by
        obtain ⟨a, rfl⟩ := hq r
        exact (isUnit_of_map_unit f.hom a hr).map q⟩
      residue_comm := fun r ↦ by
        obtain ⟨a, rfl⟩ := hq r
        exact (f.residue_comm a).trans (he a).symm }
  exact ⟨I, q', j, rfl, hq, Subtype.val_injective, Subalgebra.range_val R⟩

/-- A morphism of `𝒞_Λ` whose underlying algebra homomorphism is surjective is an
epimorphism. -/
theorem ArtinianLocalAlgCat.epi_of_surjective {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ B) (hf : Function.Surjective f.hom) : Epi f := by
  refine ⟨fun g h H ↦ ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun b ↦ ?_)⟩
  obtain ⟨a, rfl⟩ := hf b
  exact DFunLike.congr_fun (congrArg ArtinianLocalAlgCat.Hom.hom H) a

/-- A morphism of `𝒞_Λ` whose underlying algebra homomorphism is injective is a
monomorphism. -/
theorem ArtinianLocalAlgCat.mono_of_injective {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ B) (hf : Function.Injective f.hom) : Mono f :=
  ⟨fun _ _ H ↦ ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a ↦
    hf (DFunLike.congr_fun (congrArg ArtinianLocalAlgCat.Hom.hom H) a))⟩

/-- In a category cofibered in groupoids, a morphism whose image is an epimorphism is itself
an epimorphism. -/
theorem epi_of_epi_map
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {a b : F} (i : a ⟶ b)
    [Epi (p.map i)] : Epi i := by
  constructor
  intro c j l h
  have hm : p.map l = p.map j := (cancel_epi (p.map i)).1 (by
    simpa only [← p.map_comp] using congrArg p.map h.symm)
  obtain ⟨m, _, hu⟩ := existsUnique_factor_of_isHomLift hp i (i ≫ j) (p.map j) (p.map_comp i j).symm
  exact (hu j ⟨rfl, rfl⟩).trans (hu l ⟨hm, h.symm⟩).symm

/-- A morphism of `𝒞_Λ` whose range is contained in the range of an injective morphism
factors through it. -/
theorem ArtinianLocalAlgCat.exists_factor_of_range_le
    {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : A ⟶ C) (j : B ⟶ C) (hj : Function.Injective j.hom)
    (h : AlgHom.range f.hom ≤ AlgHom.range j.hom) :
    ∃ q : A ⟶ B, q ≫ j = f := by
  let e := AlgEquiv.ofInjective j.hom hj
  let r := f.hom.codRestrict j.hom.range (fun a ↦ h (f.hom.mem_range_self a))
  let q := e.symm.toAlgHom.comp r
  have hq (a : A) : j.hom (q a) = f.hom a :=
    congrArg Subtype.val (e.apply_symm_apply (r a))
  refine ⟨{ hom := q
            isLocal := ⟨fun a ha ↦ isUnit_of_map_unit f.hom a
              (by rw [← hq]; exact ha.map j.hom)⟩
            residue_comm := fun a ↦ ?_ }, ?_⟩
  · rw [← j.residue_comm, hq, f.residue_comm]
  · exact ArtinianLocalAlgCat.hom_ext (AlgHom.ext hq)

private theorem base_transport {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (e : A = B) (j : B ⟶ C) (hj : Function.Injective j.hom) :
    Function.Injective (eqToHom e ≫ j).hom ∧
      AlgHom.range (eqToHom e ≫ j).hom = AlgHom.range j.hom := by
  cases e
  simpa using hj

/-- Lift the surjection onto the image, then factor the original arrow through it.
The comparison is epic, which will also enforce the functor laws. -/
private theorem push_object
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {a x : F} (h : a ⟶ x) :
    ∃ (Z : DescentObject p x) (i : a ⟶ Z.obj.left),
      Epi i ∧ i ≫ Z.obj.hom = h ∧
        AlgHom.range (p.map Z.obj.hom).hom = AlgHom.range (p.map h).hom := by
  obtain ⟨I, q, j, hqj, hq, hj, hr⟩ := image_factorization (p.map h)
  obtain ⟨z, i, hi⟩ := hp.exists_lift q.op (Opposite.op a) rfl
  let ii := i.unop
  have hiop : p.op.IsHomLift q.op i := hi
  have : p.IsHomLift q ii := isHomLift_unop p q.op i
  have hI := IsHomLift.codomain_eq p q ii
  let jj : p.obj z.unop ⟶ p.obj x := eqToHom hI ≫ j
  have hmap : p.map ii ≫ eqToHom hI = q := by
    simpa using (IsHomLift.fac p q ii).symm
  have hfac : p.map ii ≫ jj = p.map h := by
    rw [← hqj, ← hmap, Category.assoc]
  obtain ⟨l, hl, _⟩ := existsUnique_factor_of_isHomLift hp ii h jj hfac
  have hprops : Function.Injective jj.hom ∧
      AlgHom.range jj.hom = AlgHom.range (p.map h).hom :=
    ⟨(base_transport hI j hj).1, (base_transport hI j hj).2.trans hr⟩
  have : Epi (p.map ii ≫ eqToHom hI) := hmap ▸ ArtinianLocalAlgCat.epi_of_surjective q hq
  have : Epi (p.map ii) := (epi_comp_iff_of_isIso _ (eqToHom hI)).mp inferInstance
  refine ⟨⟨Over.mk l, ?_⟩, ii, epi_of_epi_map p hp ii, hl.2, ?_⟩
  · change Function.Injective (p.map l).hom
    simpa only [hl.1] using hprops.1
  · change AlgHom.range (p.map l).hom = _
    simpa only [hl.1] using hprops.2

/-- Inclusion of image subalgebras gives the base map for the induced descent morphism. -/
private theorem push_map
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {y x : F} (g : y ⟶ x)
    {X Y : DescentObject p y} {Z W : DescentObject p x}
    (i : X.obj.left ⟶ Z.obj.left) (j : Y.obj.left ⟶ W.obj.left) [Epi i]
    (hi : i ≫ Z.obj.hom = X.obj.hom ≫ g)
    (hj : j ≫ W.obj.hom = Y.obj.hom ≫ g)
    (hZ : AlgHom.range (p.map Z.obj.hom).hom =
      AlgHom.range (p.map (X.obj.hom ≫ g)).hom)
    (hW : AlgHom.range (p.map W.obj.hom).hom =
      AlgHom.range (p.map (Y.obj.hom ≫ g)).hom) (f : X ⟶ Y) :
    ∃ t : Z ⟶ W, i ≫ t.hom.left = f.hom.left ≫ j := by
  have hw : i ≫ Z.obj.hom = (f.hom.left ≫ j) ≫ W.obj.hom := by
    rw [Category.assoc, hj, ← Category.assoc, Over.w, hi]
  have hr : AlgHom.range (p.map Z.obj.hom).hom ≤
      AlgHom.range (p.map W.obj.hom).hom := by
    rw [hZ, hW, ← Over.w f.hom, Category.assoc, p.map_comp,
      ArtinianLocalAlgCat.comp_hom]
    exact AlgHom.range_comp_le_range _ _
  obtain ⟨q, hq⟩ := ArtinianLocalAlgCat.exists_factor_of_range_le (p.map Z.obj.hom)
    (p.map W.obj.hom) W.property hr
  let : Mono (p.map W.obj.hom) := ArtinianLocalAlgCat.mono_of_injective _ W.property
  have hbase : p.map i ≫ q = p.map (f.hom.left ≫ j) := by
    apply (cancel_mono (p.map W.obj.hom)).1
    rw [Category.assoc, hq, ← p.map_comp, hw, p.map_comp]
  obtain ⟨t, ht, _⟩ := existsUnique_factor_of_isHomLift hp i (f.hom.left ≫ j) q hbase
  have htW : t ≫ W.obj.hom = Z.obj.hom := by
    apply (cancel_epi i).1
    rw [← Category.assoc, ht.2, ← hw]
  exact ⟨ObjectProperty.homMk (Over.homMk t htW), ht.2⟩

private theorem pushforward_nonempty
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {y x : F} (g : y ⟶ x) :
    Nonempty (DescentPushforward p g) := by
  classical
  choose Z i hi hf hr using
    (fun X : DescentObject p y ↦ push_object p hp (X.obj.hom ≫ g))
  let (X : DescentObject p y) : Epi (i X) := hi X
  have hm (X Y : DescentObject p y) (f : X ⟶ Y) :
      ∃ t : Z X ⟶ Z Y, i X ≫ t.hom.left = f.hom.left ≫ i Y :=
    push_map p hp g (i X) (i Y) (hf X) (hf Y) (hr X) (hr Y) f
  choose m hm using hm
  refine ⟨?_⟩
  refine
    { functor :=
        { obj := Z
          map := fun {X Y} f ↦ m X Y f
          map_id := ?_
          map_comp := ?_ }
      inclusion := i
      inclusion_cocartesian := fun X ↦
        isStronglyCocartesian_of_isCofiberedInGroupoids hp (p.map (i X)) (i X)
          (IsHomLift.map p (i X))
      inclusion_fac := hf
      base_range := hr
      inclusion_naturality := fun {X Y} f ↦ hm X Y f }
  · exact fun X ↦ ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      ((cancel_epi (i X)).1 (by simpa using hm X X (𝟙 X))))
  · intro X Y T f h
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ((cancel_epi (i X)).1 ?_))
    change i X ≫ (m X T (f ≫ h)).hom.left =
      i X ≫ ((m X Y f).hom.left ≫ (m Y T h).hom.left)
    rw [hm, ← Category.assoc, hm, Category.assoc, hm]
    exact Category.assoc _ _ _

/-- Pushforward along an arrow in a category cofibered in groupoids, obtained
by factoring each base composite through its image and pushing forward along
the resulting surjection. -/
@[implicit_reducible]
noncomputable def descentPushforward
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {y x : F} (g : y ⟶ x) :
    DescentPushforward p g :=
  Classical.choice (by exact pushforward_nonempty p hp g)

end Deformation

end

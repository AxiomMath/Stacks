module

public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentVectorSpace
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.ResidueField.Basic
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.LiftsOfObjects.Action.Difference

/-!
# The tangent space of the automorphism functor at a point over the residue field

Let `p : 𝓕 ⥤ 𝒞_Λ` be a predeformation category satisfying (RS), let `x` be an object of `𝓕` over
the residue field `k` and let `P` be a choice of pushforwards of `x`. By Tag 06JX the infinitesimal
automorphisms `Inf_x(𝓕)` are the tangent space `T_{id_x} Aut(x)` of the automorphism functor at
the identity, with the natural `k`-vector space structure of Tag 06JV, whose addition is
composition of automorphisms and whose scalar multiplication is transport along the scaling
`ε ↦ cε` of the dual numbers. Over the residue field the reduction condition defining that
tangent space is empty, because a point of a predeformation category over an algebra with
residue map an isomorphism has no nontrivial automorphisms in its fibre; so `T_{id_x} Aut(x)` is
the whole automorphism group of the pushforward of `x` to the dual numbers.

The tangent space is formed with the canonical dual numbers *under `p.obj x`*. When `𝓕` lives
over `𝒞_Λ` in a single universe, these are identified with the trivial square-zero extension
`k[k]` produced by the square-zero extension functor, compatibly with the structure maps out of
the residue field and with the two scalings of the infinitesimal coordinate.

## Main definitions

* `Deformation.dualNumbersUnderHom`: the comparison of the dual numbers under `p.obj x` with
  `k[k]`; it is an isomorphism of `𝒞_Λ`.
* `Deformation.fiberAutMulEquivOfIso`: conjugation by an isomorphism between objects of two fibres
  identifies their automorphism groups.
* `Deformation.localizedTangentEquivAut`: for a point of a predeformation category, the tangent
  space at the identity of the automorphism functor is the automorphism group of the pushforward
  to the dual numbers.

## Main results

* `Deformation.dualNumbersUnder_hom_comp_dualNumbersUnderHom`,
  `Deformation.tangentScaling_right_comp_dualNumbersUnderHom`: the comparison respects the
  inclusion of the residue field and intertwines the scalings.
* `Deformation.nonempty_iso_of_isIso_residueMorphism`,
  `Deformation.subsingleton_aut_of_isIso_residueMorphism`: an object of a predeformation
  category over an algebra whose residue map is an isomorphism is isomorphic to every point
  over the residue field, and has no nontrivial automorphisms in its fibre.
* `Deformation.localizedTangentEquivAut_add`, `Deformation.localizedTangentEquivAut_smul`: the
  vector space structure of Tag 06JV, read on automorphisms.

## References

* [Stacks Project, Tag 06GS](https://stacks.math.columbia.edu/tag/06GS)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JX](https://stacks.math.columbia.edu/tag/06JX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

namespace Deformation

section DualNumbersUnder

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type*} [Category F] {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k} {x : F}

/-- The ring map identifying the canonical dual numbers under `p.obj x` with the trivial
square-zero extension of `k` by itself. -/
def dualNumbersUnderRingHom :
    ↑(dualNumbersUnder (p := p) (x := x)).right →+*
      ↑((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)) :=
  letI := residueAlgebra (p.obj x)
  ((squareZeroExtensionArtinian.{u, u, u} (p.obj x) k).map
    (FGModuleCat.ofHom (ULift.moduleEquiv.{u, u, u} (R := k) (M := k)).toLinearMap)).hom.toRingHom

/-- The comparison does not move the residue coordinate. -/
theorem dualNumbersUnderRingHom_fst (a : TrivSqZeroExt k (ULift.{u} k)) :
    TrivSqZeroExt.fst (dualNumbersUnderRingHom (p := p) (x := x) a) = a.fst := by
  change TrivSqZeroExt.fst (TrivSqZeroExt.map
    (ULift.moduleEquiv.{u, u, u} (R := k) (M := k)).toLinearMap a) = _
  exact TrivSqZeroExt.fst_map _ _

/-- The comparison acts on the infinitesimal coordinate by forgetting the universe lift. -/
theorem dualNumbersUnderRingHom_snd (a : TrivSqZeroExt k (ULift.{u} k)) :
    TrivSqZeroExt.snd (dualNumbersUnderRingHom (p := p) (x := x) a) = a.snd.down := by
  change TrivSqZeroExt.snd (TrivSqZeroExt.map
    (ULift.moduleEquiv.{u, u, u} (R := k) (M := k)).toLinearMap a) = _
  exact TrivSqZeroExt.snd_map _ _

/-- The canonical dual numbers under `p.obj x`, compared with the trivial square-zero extension
of `k` by itself. -/
def dualNumbersUnderHom :
    (dualNumbersUnder (p := p) (x := x)).right ⟶
      (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k) :=
  homOfRingHom (dualNumbersUnderRingHom (p := p) (x := x))
    (fun t => TrivSqZeroExt.ext
      ((dualNumbersUnderRingHom_fst (p := p) (x := x) _).trans ((p.obj x).residueEquiv.commutes t))
      ((dualNumbersUnderRingHom_snd (p := p) (x := x) _).trans rfl))
    (fun a => dualNumbersUnderRingHom_fst (p := p) (x := x) a)

/-- The comparison acts on elements by the underlying ring map. -/
theorem dualNumbersUnderHom_hom_apply (a : (dualNumbersUnder (p := p) (x := x)).right) :
    (dualNumbersUnderHom (p := p) (x := x)).hom a = dualNumbersUnderRingHom (p := p) (x := x) a :=
  rfl

/-- The comparison is bijective. -/
theorem dualNumbersUnderHom_bijective :
    Function.Bijective (dualNumbersUnderHom (p := p) (x := x)).hom := by
  constructor
  · intro a b h
    rw [dualNumbersUnderHom_hom_apply, dualNumbersUnderHom_hom_apply] at h
    exact TrivSqZeroExt.ext
      ((dualNumbersUnderRingHom_fst (p := p) (x := x) a).symm.trans
        ((congrArg TrivSqZeroExt.fst h).trans (dualNumbersUnderRingHom_fst (p := p) (x := x) b)))
      (ULift.ext ((dualNumbersUnderRingHom_snd (p := p) (x := x) a).symm.trans
        ((congrArg TrivSqZeroExt.snd h).trans (dualNumbersUnderRingHom_snd (p := p) (x := x) b))))
  · intro b
    let b' : TrivSqZeroExt k k := b
    refine ⟨((b'.fst, ULift.up b'.snd) : TrivSqZeroExt k (ULift.{u} k)), ?_⟩
    refine (dualNumbersUnderHom_hom_apply _).trans ?_
    exact TrivSqZeroExt.ext (dualNumbersUnderRingHom_fst (p := p) (x := x) _)
      (dualNumbersUnderRingHom_snd (p := p) (x := x) _)

/-- The comparison is an isomorphism of `𝒞_Λ`. -/
instance : IsIso (dualNumbersUnderHom (p := p) (x := x)) :=
  ArtinianLocalAlgCat.isIso_of_bijective_hom _ dualNumbersUnderHom_bijective

/-- Two maps into a trivial square-zero extension of `k` are equal when they agree on the
infinitesimal coordinate. -/
private theorem hom_ext_of_snd_eq {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {V : FGModuleCat k} {f g : A ⟶ (artinianSquareZeroExtensionFunctor Λ k).obj V}
    (h : ∀ a, TrivSqZeroExt.snd (f.hom a) = TrivSqZeroExt.snd (g.hom a)) : f = g := by
  apply ArtinianLocalAlgCat.hom_ext
  ext a
  exact TrivSqZeroExt.ext ((f.residue_comm a).trans (g.residue_comm a).symm) (h a)

/-- The structure map of the canonical dual numbers under `p.obj x`, followed by the comparison
with `k[k]`, is the inclusion of the residue field: it factors through every map to the trivial
square-zero extension by the zero space. -/
theorem dualNumbersUnder_hom_comp_dualNumbersUnderHom
    (m : p.obj x ⟶ (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k PUnit.{u + 1})) :
    (dualNumbersUnder (p := p) (x := x)).hom ≫ dualNumbersUnderHom (p := p) (x := x) =
      m ≫ (artinianSquareZeroExtensionFunctor Λ k).map 0 := by
  refine hom_ext_of_snd_eq fun a => ?_
  refine (dualNumbersUnderRingHom_snd (p := p) (x := x) _).trans ?_
  exact (squareZeroExtensionArtinian_map_snd (Λ := Λ) (V := FGModuleCat.of k PUnit.{u + 1})
    (W := FGModuleCat.of k k) 0 (m.hom a)).symm

/-- The comparison with `k[k]` intertwines the scaling of the infinitesimal coordinate. -/
theorem tangentScaling_right_comp_dualNumbersUnderHom (c : k) :
    (tangentScaling (p := p) (x := x) c).right ≫ dualNumbersUnderHom (p := p) (x := x) =
      dualNumbersUnderHom (p := p) (x := x) ≫
        (artinianSquareZeroExtensionFunctor Λ k).map (c • 𝟙 (FGModuleCat.of k k)) := by
  refine hom_ext_of_snd_eq fun a => ?_
  refine (dualNumbersUnderRingHom_snd (p := p) (x := x) _).trans ?_
  refine Eq.trans ?_ (squareZeroExtensionArtinian_map_snd (Λ := Λ)
    (V := FGModuleCat.of k k) (W := FGModuleCat.of k k) _ _).symm
  let := residueAlgebra (p.obj x)
  refine (congrArg ULift.down
    (squareZeroExtensionArtinian_map_snd (Λ := p.obj x) _ a)).trans ?_
  exact congrArg (c • ·) (dualNumbersUnderRingHom_snd (p := p) (x := x) a).symm

end DualNumbersUnder

/-! ### Automorphisms in the fibres of a functor -/

section FiberAut

open Functor

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {C : Type*} [Category C] {E : Type*} [Category E] {p : E ⥤ C}

/-- An endomorphism of an object of a fibre lies over the identity. -/
theorem map_fiber_hom_val_eq_id {U : C} {a : p.Fiber U} (f : a ⟶ a) : p.map f.1 = 𝟙 _ := by
  have := f.2
  rw [IsHomLift.fac' p (𝟙 U) f.1]
  simp

/-- An endomorphism of the underlying object of an object of a fibre whose image is an identity
is a morphism of that fibre. -/
def fiberEndMk {U : C} {a : p.Fiber U} (f : a.1 ⟶ a.1) (hf : p.map f = 𝟙 _) : a ⟶ a :=
  ⟨f, IsHomLift.of_fac' p (𝟙 U) f a.2 a.2 (by rw [hf]; simp)⟩

omit [Category C] in
/-- Conjugates of mutually inverse endomorphisms are mutually inverse. -/
private theorem conj_comp_conj {X Y : E} (e : X ≅ Y) {f g : X ⟶ X} (h : f ≫ g = 𝟙 X) :
    (e.inv ≫ f ≫ e.hom) ≫ e.inv ≫ g ≫ e.hom = 𝟙 Y := by
  simp [reassoc_of% h]

/-- Conjugation by an isomorphism of the total category between objects of two fibres
identifies their automorphism groups. -/
def fiberAutMulEquivOfIso {U V : C} {a : p.Fiber U} {b : p.Fiber V} (e : a.1 ≅ b.1) :
    Aut a ≃* Aut b where
  toFun α := .of
    { hom := fiberEndMk (e.inv ≫ α.asIso.hom.1 ≫ e.hom) (by
        rw [p.map_comp, p.map_comp, map_fiber_hom_val_eq_id, Category.id_comp, ← p.map_comp,
          e.inv_hom_id, p.map_id])
      inv := fiberEndMk (e.inv ≫ α.asIso.inv.1 ≫ e.hom) (by
        rw [p.map_comp, p.map_comp, map_fiber_hom_val_eq_id, Category.id_comp, ← p.map_comp,
          e.inv_hom_id, p.map_id])
      hom_inv_id := Fiber.hom_ext <| by
        exact conj_comp_conj e (congrArg Subtype.val α.asIso.hom_inv_id)
      inv_hom_id := Fiber.hom_ext <| by
        exact conj_comp_conj e (congrArg Subtype.val α.asIso.inv_hom_id) }
  invFun β := .of
    { hom := fiberEndMk (e.hom ≫ β.asIso.hom.1 ≫ e.inv) (by
        rw [p.map_comp, p.map_comp, map_fiber_hom_val_eq_id, Category.id_comp, ← p.map_comp,
          e.hom_inv_id, p.map_id])
      inv := fiberEndMk (e.hom ≫ β.asIso.inv.1 ≫ e.inv) (by
        rw [p.map_comp, p.map_comp, map_fiber_hom_val_eq_id, Category.id_comp, ← p.map_comp,
          e.hom_inv_id, p.map_id])
      hom_inv_id := Fiber.hom_ext <| by
        exact conj_comp_conj e.symm (congrArg Subtype.val β.asIso.hom_inv_id)
      inv_hom_id := Fiber.hom_ext <| by
        exact conj_comp_conj e.symm (congrArg Subtype.val β.asIso.inv_hom_id) }
  left_inv α := by
    apply Aut.ext; apply Iso.ext
    apply Fiber.hom_ext
    change e.hom ≫ (e.inv ≫ α.asIso.hom.1 ≫ e.hom) ≫ e.inv = α.asIso.hom.1
    simp
  right_inv β := by
    apply Aut.ext; apply Iso.ext
    apply Fiber.hom_ext
    change e.inv ≫ (e.hom ≫ β.asIso.hom.1 ≫ e.inv) ≫ e.hom = β.asIso.hom.1
    simp
  map_mul' α α' := by
    apply Aut.ext; apply Iso.ext
    apply Fiber.hom_ext
    change e.inv ≫ (α'.asIso.hom.1 ≫ α.asIso.hom.1) ≫ e.hom =
      (e.inv ≫ α'.asIso.hom.1 ≫ e.hom) ≫ e.inv ≫ α.asIso.hom.1 ≫ e.hom
    simp

/-- The conjugate automorphism is conjugation by the given isomorphism. -/
@[simp]
theorem fiberAutMulEquivOfIso_hom_val {U V : C} {a : p.Fiber U} {b : p.Fiber V} (e : a.1 ≅ b.1)
    (α : Aut a) : (fiberAutMulEquivOfIso e α).asIso.hom.1 = e.inv ≫ α.asIso.hom.1 ≫ e.hom :=
  rfl

end FiberAut

/-! ### Points over residue-field objects of a predeformation category -/

section ResidueFieldPoints

open Functor

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type*} [Category F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- In a predeformation category, a point over the residue field is isomorphic to every object
lying over an Artinian algebra whose residue map is an isomorphism. -/
theorem nonempty_iso_of_isIso_residueMorphism (hp : IsPredeformationCategory p)
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) (y : F)
    [IsIso (residueMorphism.{u, v, w} (p.obj y))] : Nonempty (x.1 ≅ y) := by
  let L := cofiberedFiberLift p hp.cofibered (residueMorphism.{u, v, w} (p.obj y)) ⟨y, rfl⟩
  have : p.IsHomLift (residueMorphism.{u, v, w} (p.obj y)) L.2.1 := L.2.2
  have : p.IsStronglyCocartesian (residueMorphism.{u, v, w} (p.obj y)) L.2.1 :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp.cofibered _ _ L.2.2
  have : IsIso L.2.1 :=
    IsStronglyCocartesian.isIso_of_base_isIso p (residueMorphism.{u, v, w} (p.obj y)) L.2.1
  obtain ⟨f, -, -⟩ := existsUnique_pointIso hp x L.1
  exact ⟨Fiber.fiberInclusion.mapIso f ≪≫ (asIso L.2.1).symm⟩

/-- In a predeformation category, an object lying over an Artinian algebra whose residue map is
an isomorphism has no nontrivial automorphisms in its fibre. -/
theorem subsingleton_aut_of_isIso_residueMorphism (hp : IsPredeformationCategory p)
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} [IsIso (residueMorphism.{u, v, w} A)]
    (y : p.Fiber A) : Subsingleton (Aut y) := by
  obtain ⟨E⟩ := hp.specialFiber
  let x := E.inverse.obj ⟨⟨⟩⟩
  obtain ⟨y, rfl⟩ := y
  obtain ⟨e⟩ := nonempty_iso_of_isIso_residueMorphism hp x y
  have := subsingleton_aut_residueField hp x
  exact (fiberAutMulEquivOfIso (p := p) (a := x) (b := ⟨y, rfl⟩) e).symm.toEquiv.subsingleton

/-- The residue-field object under the base of an object is a residue-field object. -/
instance isIso_residueMorphism_specialFibreUnder (x : F) :
    IsIso (residueMorphism.{u, v, w} (specialFibreUnder (p := p) (x := x)).right) := by
  let := residueAlgebra (p.obj x)
  let r := residueMorphism.{u, v, w} (specialFibreUnder (p := p) (x := x)).right
  have hr (a : (specialFibreUnder (p := p) (x := x)).right) : r.hom a = ULift.up a.down :=
    ULift.ext (residueFieldObject_residue (p.obj x) k a)
  refine ArtinianLocalAlgCat.isIso_of_bijective_hom r ⟨fun a b hab => ?_, fun a => ⟨⟨a.down⟩, hr _⟩⟩
  exact ULift.ext (congrArg ULift.down ((hr a).symm.trans (hab.trans (hr b))))

end ResidueFieldPoints

/-! ### The tangent space of the automorphism functor at a point -/

section LocalizedTangent

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type*} [Category F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {x : F} (P : ChosenPushforwardsAt p x)

/-- In a predeformation category every automorphism of the pushforward to the dual numbers
reduces to the identity on the residue field. -/
theorem ker_transportAutHom_tangentReduction (hp : IsPredeformationCategory p) :
    MonoidHom.ker (P.transportAutHom (tangentReduction (p := p) (x := x))) = ⊤ := by
  have := subsingleton_aut_of_isIso_residueMorphism hp
    (P.obj (specialFibreUnder (p := p) (x := x)))
  exact (Subgroup.eq_top_iff' _).2 fun a => Subsingleton.elim _ _

/-- In a predeformation category, the tangent space at the identity of the automorphism functor
is the group of all automorphisms of the pushforward to the dual numbers. -/
def localizedTangentEquivAut (hp : IsPredeformationCategory p) :
    localizedAutomorphismFunctorTangent P ≃ Aut (P.obj (dualNumbersUnder (p := p) (x := x))) :=
  (localizedTangentEquivKernel P).trans
    ((MulEquiv.subgroupCongr (ker_transportAutHom_tangentReduction P hp)).trans
      Subgroup.topEquiv).toEquiv

/-- The identification sends a tangent vector to the automorphism underlying its image in the
kernel of the reduction. -/
theorem localizedTangentEquivAut_apply (hp : IsPredeformationCategory p)
    (a : localizedAutomorphismFunctorTangent P) :
    localizedTangentEquivAut P hp a = (localizedTangentEquivKernel P a).1 :=
  rfl

/-- Addition on the tangent space at the identity of the automorphism functor is composition of
automorphisms. -/
theorem localizedTangentEquivAut_add (hp : IsPredeformationCategory p) (hRS : SatisfiesRS p)
    (a b : localizedAutomorphismFunctorTangent P) :
    letI := naturalLocalizedTangentAddCommGroup P hRS
    localizedTangentEquivAut P hp (a + b) =
      localizedTangentEquivAut P hp a * localizedTangentEquivAut P hp b :=
  congrArg Subtype.val ((naturalLocalizedTangentModule_spec P hRS).1 a b)

/-- Scalar multiplication on the tangent space at the identity of the automorphism functor is
transport along the scaling of the infinitesimal coordinate. -/
theorem localizedTangentEquivAut_smul (hp : IsPredeformationCategory p) (hRS : SatisfiesRS p)
    (c : k) (a : localizedAutomorphismFunctorTangent P) :
    letI := naturalLocalizedTangentAddCommGroup P hRS
    letI := naturalLocalizedTangentModule P hRS
    localizedTangentEquivAut P hp (c • a) =
      P.transportAutHom (tangentScaling (p := p) (x := x) c) (localizedTangentEquivAut P hp a) :=
  (naturalLocalizedTangentModule_spec P hRS).2 c a

end LocalizedTangent

end Deformation

end

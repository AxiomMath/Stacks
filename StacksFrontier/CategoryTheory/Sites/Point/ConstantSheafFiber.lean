module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# The fibre of a constant sheaf at a point of a site

Let `(C, J)` be a site and let `Φ` be a point of it. The fibre of a presheaf at `Φ` is a colimit
over the category of neighbourhoods of `Φ`, which is cofiltered, hence connected; so the fibre of
a *constant* presheaf is its value. The map from a presheaf to its sheafification is locally
bijective, and fibres do not distinguish a presheaf from its associated sheaf, so the fibre of a
constant *sheaf* is again its value.

The last result of the file is an application of this identification: if a sheaf `G` sits
between the sheafifications of the constant presheaves on `A'` and on `A`, and the first map is
an isomorphism on the fibre at `Φ`, then every section of `G` over a neighbourhood of `Φ` whose
image downstream is constant has its constant value already in `A'`.

## Main definitions

* `CategoryTheory.Sites.constantPresheafFiberIso`: the fibre of a constant presheaf is its value.
* `CategoryTheory.Sites.constantSheafFiberIso`: the fibre of a constant sheaf is its value.
* `CategoryTheory.Sites.constantPresheafFiberNatIso`,
  `CategoryTheory.Sites.constantSheafFiberNatIso`: the same identifications, natural in the value;
  the second one asks for no concreteness of the coefficients.

## Main results

* `CategoryTheory.Sites.constantPresheafFiberIso_ι`: every canonical map from a value of a
  constant presheaf to its fibre is a section of the identification.
* `CategoryTheory.Sites.constantSheafFiberIso_naturality`: the identification is natural in the
  value.
* `CategoryTheory.Sites.constantSheafFiberIso_toSheafify_app`: the identification sends the image
  of a constant under the sheafification map back to that constant.
* `CategoryTheory.Sites.exists_preimage_of_stalk_value`: a constant section of the ambient sheaf
  which factors through an intermediate sheaf whose fibre is already that of the subobject has
  its value in the subobject.

## Implementation notes

The fibre of a sheaf is computed through the fibre of the underlying presheaf rather than through
`CategoryTheory.GrothendieckTopology.Point.sheafFiber`, because the comparison with the constant
presheaf is a statement about the sheafification map, which lives at the level of presheaves.

The constant sheaf is written as the sheafification of the constant presheaf rather than as
`CategoryTheory.constantSheaf`: the two agree by definition, but only the former is reducibly
the sheafification, which is what the local bijectivity instances and the rewriting below match
against.

## References

* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Sites

open Limits Opposite GrothendieckTopology

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

section Presheaf

variable {D : Type u₂} [Category.{v₂} D] [HasColimitsOfSize.{w, w} D]

/-- The cocone, on a constant presheaf viewed over the neighbourhoods of a point of a site, all
of whose legs are the identity. -/
noncomputable def constPresheafCocone (Φ : J.Point.{w}) (A : D) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ (Functor.const Cᵒᵖ).obj A) :=
  Limits.constCocone Φ.fiber.Elementsᵒᵖ A

/-- The all-identity cocone on a constant presheaf over the neighbourhoods of a point of a site
is a colimit cocone, because the neighbourhoods form a connected category. -/
noncomputable def isColimitConstPresheafCocone (Φ : J.Point.{w}) (A : D) :
    IsColimit (constPresheafCocone Φ A) :=
  have : IsConnected Φ.fiber.Elementsᵒᵖ := IsFiltered.isConnected _
  Limits.isColimitConstCocone Φ.fiber.Elementsᵒᵖ A

/-- The fibre of a constant presheaf at a point of a site is its value: the fibre is a colimit
over the neighbourhoods of the point, and that category is connected. -/
noncomputable def constantPresheafFiberIso (Φ : J.Point.{w}) (A : D) :
    Φ.presheafFiber.obj ((Functor.const Cᵒᵖ).obj A) ≅ A :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstPresheafCocone Φ A)

/-- Every canonical map from the value of a constant presheaf over a neighbourhood of a point to
the fibre at that point is a section of `CategoryTheory.Sites.constantPresheafFiberIso`. -/
theorem constantPresheafFiberIso_ι (Φ : J.Point.{w}) (A : D) (V : C) (q : Φ.fiber.obj V) :
    Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj A) ≫ (constantPresheafFiberIso Φ A).hom =
      𝟙 A :=
  colimit.comp_coconePointUniqueUpToIso_hom (isColimitConstPresheafCocone Φ A)
    (op (⟨V, q⟩ : Φ.fiber.Elements))

/-- The identification of the fibre at a point of the site of a constant presheaf with its value
is natural in the value. -/
theorem constantPresheafFiberIso_naturality (Φ : J.Point.{w}) {A B : D} (f : A ⟶ B) :
    (constantPresheafFiberIso Φ A).hom ≫ f =
      Φ.presheafFiber.map ((Functor.const Cᵒᵖ).map f) ≫ (constantPresheafFiberIso Φ B).hom := by
  apply Φ.presheafFiber_hom_ext
  intro V q
  calc Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj A) ≫
          (constantPresheafFiberIso Φ A).hom ≫ f
      = (Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj A) ≫
          (constantPresheafFiberIso Φ A).hom) ≫ f := by rw [Category.assoc]
    _ = ((Functor.const Cᵒᵖ).map f).app (op V) ≫
          (Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj B) ≫
            (constantPresheafFiberIso Φ B).hom) := by
          rw [constantPresheafFiberIso_ι, constantPresheafFiberIso_ι]
          simp
    _ = Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj A) ≫
          Φ.presheafFiber.map ((Functor.const Cᵒᵖ).map f) ≫
            (constantPresheafFiberIso Φ B).hom := by
          rw [← Category.assoc, ← Φ.toPresheafFiber_naturality, Category.assoc]

/-- The fibre at a point of the site of a constant presheaf is its value, naturally in the
value. -/
noncomputable def constantPresheafFiberNatIso (Φ : J.Point.{w}) :
    (Functor.const Cᵒᵖ : D ⥤ _) ⋙ Φ.presheafFiber ≅ 𝟭 D :=
  NatIso.ofComponents (fun M => constantPresheafFiberIso Φ M)
    (fun f => (constantPresheafFiberIso_naturality Φ f).symm)

/-- The fibre at a point of the site of a constant sheaf, with values in a category having
products and colimits indexed by the universe of the point, is its value, naturally in the value.

No concreteness of the coefficients is needed, unlike for
`CategoryTheory.Sites.constantSheafFiberIso`: the fibre functor on sheaves is a localization of
the fibre functor on presheaves at the morphisms that sheafification inverts, so the
sheafification map of a constant presheaf is invertible on fibres for that reason alone. -/
noncomputable def constantSheafFiberNatIso [HasProducts.{w} D] [HasWeakSheafify J D]
    (Φ : J.Point.{w}) :
    constantSheaf J D ⋙ Φ.sheafFiber ≅ 𝟭 D :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ) (Φ.presheafToSheafCompSheafFiberIso D) ≪≫
      constantPresheafFiberNatIso Φ

/-- The fibre of a morphism of presheaves sends the germ of a section to the germ of its image. -/
private theorem presheafFiber_map_toPresheafFiber_apply {FD : D → D → Type*} {CD : D → Type v₂}
    [∀ A B, FunLike (FD A B) (CD A) (CD B)] [ConcreteCategory.{v₂} D FD] (Φ : J.Point.{w})
    {P Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (V : C) (q : Φ.fiber.obj V) (a : CD (P.obj (op V))) :
    Φ.presheafFiber.map f (Φ.toPresheafFiber V q P a) =
      Φ.toPresheafFiber V q Q (f.app (op V) a) := by
  simp

end Presheaf

section Sheaf

variable {D : Type u₂} {FD : D → D → Type*} {CD : D → Type v₂}
  [∀ A B, FunLike (FD A B) (CD A) (CD B)] [Category.{v₂} D] [ConcreteCategory.{v₂} D FD]
  [LocallySmall.{w} C] [HasWeakSheafify J D] [J.WEqualsLocallyBijective D]
  [UnivLE.{w, v₂}] [PreservesFilteredColimitsOfSize.{v₂, v₂} (forget D)]
  [(forget D).ReflectsIsomorphisms] [HasColimitsOfSize.{w, w} D]

include FD CD

/-- The sheafification map of a constant presheaf induces an isomorphism on the fibre at a point
of the site, because it is locally bijective. -/
theorem isIso_presheafFiber_map_toSheafify (Φ : J.Point.{w}) (A : D) :
    IsIso (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A))) := by
  have : PreservesFilteredColimitsOfSize.{w, w} (forget D) :=
    preservesFilteredColimitsOfSize_of_univLE (forget D)
  have : IsIso ((forget D).map
      (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)))) :=
    (bijective_iff_isIso_ofHom _).mp
      (Φ.toPresheafFiber_map_bijective (toSheafify J ((Functor.const Cᵒᵖ).obj A)))
  exact isIso_of_reflects_iso _ (forget D)

/-- The fibre of a constant sheaf at a point of a site is its value: sheafification does not
change the fibre, and the fibre of the constant presheaf is the value. -/
noncomputable def constantSheafFiberIso (Φ : J.Point.{w}) (A : D) :
    Φ.presheafFiber.obj (sheafify J ((Functor.const Cᵒᵖ).obj A)) ≅ A :=
  have := isIso_presheafFiber_map_toSheafify Φ A
  (asIso (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)))).symm ≪≫
    constantPresheafFiberIso Φ A

/-- The sheafification map, read through `CategoryTheory.Sites.constantSheafFiberIso`, is the
identification of the fibre of the constant presheaf. -/
theorem presheafFiber_map_toSheafify_comp_constantSheafFiberIso (Φ : J.Point.{w}) (A : D) :
    Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)) ≫
        (constantSheafFiberIso Φ A).hom =
      (constantPresheafFiberIso Φ A).hom := by
  have := isIso_presheafFiber_map_toSheafify Φ A
  simp only [constantSheafFiberIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]

/-- The identification of the fibre of a constant sheaf with its value is natural in the
value. -/
theorem constantSheafFiberIso_naturality (Φ : J.Point.{w}) {A B : D} (f : A ⟶ B) :
    (constantSheafFiberIso Φ A).hom ≫ f =
      Φ.presheafFiber.map (sheafifyMap J ((Functor.const Cᵒᵖ).map f)) ≫
        (constantSheafFiberIso Φ B).hom := by
  have := isIso_presheafFiber_map_toSheafify Φ A
  have hunit : Φ.presheafFiber.map ((Functor.const Cᵒᵖ).map f) ≫
      Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj B)) =
        Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)) ≫
          Φ.presheafFiber.map (sheafifyMap J ((Functor.const Cᵒᵖ).map f)) := by
    rw [← Φ.presheafFiber.map_comp, ← Φ.presheafFiber.map_comp,
      toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)]
  have hconst := constantPresheafFiberIso_naturality Φ f
  apply (cancel_epi (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)))).mp
  rw [← Category.assoc, presheafFiber_map_toSheafify_comp_constantSheafFiberIso, hconst,
    ← presheafFiber_map_toSheafify_comp_constantSheafFiberIso Φ B, ← Category.assoc, hunit,
    Category.assoc]

/-- The identification of the fibre of a constant sheaf with its value sends the image of a
constant under the sheafification map back to that constant. -/
theorem constantSheafFiberIso_toSheafify_app (Φ : J.Point.{w}) (A : D) (V : C)
    (q : Φ.fiber.obj V) (a : CD A) :
    (constantSheafFiberIso Φ A).hom (Φ.toPresheafFiber V q (sheafify J ((Functor.const Cᵒᵖ).obj A))
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op V) a)) = a := by
  have hkey : Φ.toPresheafFiber V q ((Functor.const Cᵒᵖ).obj A) ≫
      Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)) ≫
        (constantSheafFiberIso Φ A).hom = 𝟙 A := by
    rw [presheafFiber_map_toSheafify_comp_constantSheafFiberIso, constantPresheafFiberIso_ι]
  rw [← presheafFiber_map_toPresheafFiber_apply]
  simpa using ConcreteCategory.congr_hom hkey a

/-- Let `G` be a sheaf fitting between the sheafifications of the constant presheaves on `A'` and
on `A` over a map `m : A' ⟶ A`, and suppose the first map is an isomorphism on the fibre at a
point `Φ`. Then a section of `G` whose image downstream is the constant `a` over a neighbourhood
of `Φ` has `a` in the image of `m`. -/
theorem exists_preimage_of_stalk_value (Φ : J.Point.{w}) {A' A : D} (m : A' ⟶ A) (G : Sheaf J D)
    (i : (presheafToSheaf J D).obj ((Functor.const Cᵒᵖ).obj A') ⟶ G)
    (j : G ⟶ (presheafToSheaf J D).obj ((Functor.const Cᵒᵖ).obj A))
    (hij : i ≫ j = (presheafToSheaf J D).map ((Functor.const Cᵒᵖ).map m))
    (hstalk : IsIso (Φ.presheafFiber.map i.hom)) (V : C) (q : Φ.fiber.obj V)
    (g : CD (G.obj.obj (op V))) (a : CD A)
    (hg : j.hom.app (op V) g = (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op V) a) :
    ∃ b : CD A', m b = a := by
  have : PreservesFilteredColimitsOfSize.{w, w} (forget D) :=
    preservesFilteredColimitsOfSize_of_univLE (forget D)
  have := hstalk
  set e := Φ.presheafFiber.map i.hom with he
  set xG := Φ.toPresheafFiber V q G.obj g with hxG
  set x := (inv e) xG with hx
  obtain ⟨y, hy⟩ := Φ.toPresheafFiber_map_surjective
    (toSheafify J ((Functor.const Cᵒᵖ).obj A')) x
  obtain ⟨W, r, b, rfl⟩ := Φ.toPresheafFiber_jointly_surjective y
  refine ⟨b, ?_⟩
  have hxW : x = Φ.toPresheafFiber W r (sheafify J ((Functor.const Cᵒᵖ).obj A'))
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A')).app (op W) b) := by
    rw [← hy, presheafFiber_map_toPresheafFiber_apply]
  have hb : (constantSheafFiberIso Φ A').hom x = b := by
    rw [hxW]
    exact constantSheafFiberIso_toSheafify_app Φ A' W r b
  have hcomp : e ≫ Φ.presheafFiber.map j.hom =
      Φ.presheafFiber.map (sheafifyMap J ((Functor.const Cᵒᵖ).map m)) := by
    rw [he, ← Φ.presheafFiber.map_comp]
    exact congrArg Φ.presheafFiber.map
      (congrArg (fun k : (presheafToSheaf J D).obj ((Functor.const Cᵒᵖ).obj A') ⟶
        (presheafToSheaf J D).obj ((Functor.const Cᵒᵖ).obj A) => k.hom) hij)
  have hex : e x = xG := by
    rw [hx]
    simp
  have hmid : Φ.presheafFiber.map (sheafifyMap J ((Functor.const Cᵒᵖ).map m)) x =
      Φ.toPresheafFiber V q (sheafify J ((Functor.const Cᵒᵖ).obj A)) (j.hom.app (op V) g) := by
    have h := ConcreteCategory.congr_hom hcomp x
    simp only [CategoryTheory.comp_apply] at h
    rw [← h, hex, hxG, presheafFiber_map_toPresheafFiber_apply]
  have hnatIso := ConcreteCategory.congr_hom (constantSheafFiberIso_naturality Φ m) x
  simp only [CategoryTheory.comp_apply] at hnatIso
  rw [hb] at hnatIso
  rw [hnatIso, hmid, hg]
  exact constantSheafFiberIso_toSheafify_app Φ A V q a

end Sheaf

end CategoryTheory.Sites

end

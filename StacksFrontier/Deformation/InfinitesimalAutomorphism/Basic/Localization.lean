module

public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic.Independence

/-!
# Infinitesimal automorphisms of a localization

The identification of the infinitesimal automorphism group of a predeformation category with
that of its localization at an object (Tag 06JS).
-/

@[expose] public section

namespace Deformation

/-! ### Infinitesimal automorphisms of a localization -/

section
open CategoryTheory
universe u v w u₁ v₁

/-- The functor from the fibre of `objectsOverFunctor p x` over `A` to the fibre of `p` over
`A` forgetting the arrow to `x`. -/
private abbrev objectsOverFiberForget {F C : Type*} [Category* F] [Category* C]
    (p : F ⥤ C) (x : F) (A : C) :
    (objectsOverFunctor p x).Fiber A ⥤ p.Fiber A where
  obj Y := ⟨Y.1.left, by simpa using Y.2⟩
  map {Y Z} f := ⟨f.1.left, by
    let : (objectsOverFunctor p x).IsHomLift (𝟙 A) f.1 := f.2
    apply IsHomLift.of_fac' (p := p) (𝟙 A) f.1.left Y.2 Z.2
    simpa [objectsOverFunctor] using IsHomLift.fac' (objectsOverFunctor p x) (𝟙 A) f.1⟩

/-- Forgetting the arrow to `x` is injective on automorphisms. -/
private lemma objectsOverFiberForget_mapAut_injective {F C : Type*} [Category* F] [Category* C]
    {p : F ⥤ C} {x : F} {A : C}
    (y : (objectsOverFunctor p x).Fiber A) :
    Function.Injective ((objectsOverFiberForget p x A).mapAut y) := by
  intro a b hm
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  apply CostructuredArrow.hom_ext
  exact congrArg (fun z : Aut ((objectsOverFiberForget p x A).obj y) => z.asIso.hom.val) hm

/-- An automorphism of the underlying object commuting with the arrow to `x` lifts to an
automorphism of an object of the fibre of `objectsOverFunctor p x`. -/
private lemma exists_objectsOverFiberForget_mapAut_eq {F C : Type*} [Category* F] [Category* C]
    {p : F ⥤ C} {x : F} {A : C}
    (y : (objectsOverFunctor p x).Fiber A) (b : Aut ((objectsOverFiberForget p x A).obj y))
    (hw : b.asIso.hom.val ≫ y.1.hom = y.1.hom) :
    ∃ a : Aut y, (objectsOverFiberForget p x A).mapAut y a = b := by
  let αO : y.1 ≅ y.1 := Over.isoMk (Functor.Fiber.fiberInclusion.mapIso b.asIso) hw
  have hαhom : αO.hom.left = b.asIso.hom.val := by
    simp [αO, Functor.Fiber.fiberInclusion, Functor.mapIso]
  have hαinv : αO.inv.left = b.asIso.inv.val := by
    simp [αO, Functor.Fiber.fiberInclusion, Functor.mapIso]
  have hlift (f : y.1 ⟶ y.1) (c : (objectsOverFiberForget p x A).obj y ⟶
        (objectsOverFiberForget p x A).obj y)
      (hf : f.left = c.val) : (objectsOverFunctor p x).IsHomLift (𝟙 A) f := by
    apply IsHomLift.of_fac' (p := objectsOverFunctor p x) (𝟙 A) f y.2 y.2
    let : p.IsHomLift (𝟙 A) c.val := c.2
    show p.map f.left = eqToHom y.2 ≫ 𝟙 A ≫ eqToHom y.2.symm
    rw [hf]
    simpa using IsHomLift.fac' p (𝟙 A) c.val
  have hqhom := hlift αO.hom b.asIso.hom hαhom
  have hqinv := hlift αO.inv b.asIso.inv hαinv
  exact ⟨.of {
    hom := ⟨αO.hom, hqhom⟩
    inv := ⟨αO.inv, hqinv⟩
    hom_inv_id := Functor.Fiber.hom_ext αO.hom_inv_id
    inv_hom_id := Functor.Fiber.hom_ext αO.inv_hom_id },
    Aut.ext (Iso.ext (Functor.Fiber.hom_ext hαhom))⟩

private lemma fiberInclusion_mapIso_eqToIso {F C : Type*} [Category* F] [Category* C]
    {p : F ⥤ C} {A : C} {X Y : p.Fiber A}
    (hx : X = Y) (hε : X.1 = Y.1) :
    Functor.Fiber.fiberInclusion.mapIso (eqToIso hx) = eqToIso hε := by
  apply Iso.ext
  cases hx
  cases hε
  rfl

private lemma eqToHom_conj_comp_eq_iff {F : Type*} [Category* F]
    {X X' Y Y' : F} (hε : X = X') (h₀ : Y = Y')
    (a : X ⟶ X) (r : X' ⟶ Y') :
    a ≫ eqToHom hε ≫ r ≫ eqToHom h₀.symm = eqToHom hε ≫ r ≫ eqToHom h₀.symm ↔
      (eqToHom hε.symm ≫ a ≫ eqToHom hε) ≫ r = r := by
  subst hε h₀
  simp

/-- The canonical retraction of `j` among objects over `x₀` is induced by the canonical
retraction of `i`. -/
private lemma canonicalRetraction_objectsOverFunctor_left
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₀ : p.Fiber (residueFieldObject Λ k)} {xε : p.Fiber Aε}
    (g : residueFieldObject Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    {y₀ : (objectsOverFunctor p x₀.1).Fiber
      (residueFieldObject Λ k)}
    {yε : (objectsOverFunctor p x₀.1).Fiber Aε}
    (j : y₀.1 ⟶ yε.1)
    (hj : (objectsOverFunctor p x₀.1).IsHomLift g j)
    (h₀ : y₀.1.left = x₀.1) (hε : yε.1.left = xε.1)
    (h₀hom : y₀.1.hom = eqToHom h₀)
    (hεhom : yε.1.hom = eqToHom hε ≫
      (canonicalRetraction hp.cofibered g e hpair.split i hi).1)
    (hjleft : j.left ≫ eqToHom hε = eqToHom h₀ ≫ i) :
    (canonicalRetraction (isPredeformationCategory_objectsOverFunctor p hp.cofibered x₀).cofibered
      g e hpair.split j hj).1.left =
      eqToHom hε ≫ (canonicalRetraction hp.cofibered g e hpair.split i hi).1 ≫
        eqToHom h₀.symm := by
  let hpq := isPredeformationCategory_objectsOverFunctor p hp.cofibered x₀
  let r := (canonicalRetraction hp.cofibered g e hpair.split i hi).1
  let rQ := (canonicalRetraction hpq.cofibered g e hpair.split j hj).1
  let he : yε.1.left ⟶ xε.1 := eqToHom hε
  let h0i : x₀.1 ⟶ y₀.1.left := eqToHom h₀.symm
  let t : yε.1.left ⟶ y₀.1.left := he ≫ r ≫ h0i
  let tQ : yε.1 ⟶ y₀.1 := Over.homMk t (by
    dsimp [t, he, h0i]
    rw [h₀hom, hεhom]
    simp [r, Category.assoc])
  have htQ : j ≫ tQ = 𝟙 y₀.1 := by
    apply CostructuredArrow.hom_ext
    show j.left ≫ t = 𝟙 y₀.1.left
    dsimp [t, he, h0i]
    calc
      j.left ≫ (eqToHom hε ≫ r ≫ eqToHom h₀.symm) =
          (j.left ≫ eqToHom hε) ≫ r ≫ eqToHom h₀.symm := by
            simp [Category.assoc]
      _ = (eqToHom h₀ ≫ i) ≫ r ≫ eqToHom h₀.symm := by rw [hjleft]
      _ = 𝟙 y₀.1.left := by
        simp [r, Category.assoc, canonicalRetraction]
  obtain ⟨_, _, huniq⟩ := existsUnique_retraction hpq.cofibered g e hpair j hj
  exact congrArg Over.Hom.left ((huniq rQ
    (canonicalRetraction hpq.cofibered g e hpair.split j hj).property.2).trans
      (huniq tQ htQ).symm)

/-- An automorphism over `x₀` is infinitesimal exactly when the induced automorphism of `xε` is. -/
private lemma mem_infinitesimalAutomorphisms_objectsOverFunctor_iff
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₀ : p.Fiber (residueFieldObject Λ k)} {xε : p.Fiber Aε}
    (g : residueFieldObject Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    {y₀ : (objectsOverFunctor p x₀.1).Fiber
      (residueFieldObject Λ k)}
    {yε : (objectsOverFunctor p x₀.1).Fiber Aε}
    (j : y₀.1 ⟶ yε.1)
    (hj : (objectsOverFunctor p x₀.1).IsHomLift g j)
    (h₀ : y₀.1.left = x₀.1) (hε : yε.1.left = xε.1)
    (h₀hom : y₀.1.hom = eqToHom h₀)
    (hεhom : yε.1.hom = eqToHom hε ≫
      (canonicalRetraction hp.cofibered g e hpair.split i hi).1)
    (hjleft : j.left ≫ eqToHom hε = eqToHom h₀ ≫ i)
    (a : Aut yε) :
    a ∈ infinitesimalAutomorphisms
        (isPredeformationCategory_objectsOverFunctor p hp.cofibered x₀).cofibered g e hpair j hj ↔
      (eqToHom hε.symm ≫ a.asIso.hom.val.left ≫ eqToHom hε) ≫
          (canonicalRetraction hp.cofibered g e hpair.split i hi).1 =
        (canonicalRetraction hp.cofibered g e hpair.split i hi).1 := by
  rw [mem_infinitesimalAutomorphisms_iff, ← eqToHom_conj_comp_eq_iff hε h₀,
    ← canonicalRetraction_objectsOverFunctor_left hp g e hpair i hi j hj h₀ hε h₀hom hεhom hjleft]
  constructor
  · intro h
    simpa using congrArg Over.Hom.left h
  · intro h
    apply CostructuredArrow.hom_ext
    simpa using h

/-- An infinitesimal automorphism of `xε` lifts to an automorphism of an object `yε` over `x₀`
whose structure map is the canonical retraction. -/
private lemma exists_conjAut_objectsOverFiberForget_mapAut_eq
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₀ : p.Fiber (residueFieldObject Λ k)} {xε : p.Fiber Aε}
    (g : residueFieldObject Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    {yε : (objectsOverFunctor p x₀.1).Fiber Aε} (hε : yε.1.left = xε.1)
    (hεhom : yε.1.hom = eqToHom hε ≫
      (canonicalRetraction hp.cofibered g e hpair.split i hi).1)
    (a : Aut xε) (ha : a ∈ infinitesimalAutomorphisms hp.cofibered g e hpair i hi) :
    ∃ b : Aut yε,
      (eqToIso (show (objectsOverFiberForget p x₀.1 Aε).obj yε = xε from Subtype.ext hε)).conjAut
        ((objectsOverFiberForget p x₀.1 Aε).mapAut yε b) = a := by
  let G := objectsOverFiberForget p x₀.1 Aε
  have hx : G.obj yε = xε := Subtype.ext hε
  let b : Aut (G.obj yε) := (eqToIso hx).conjAut.symm a
  have hb : b.asIso.hom.val ≫ eqToHom hε = eqToHom hε ≫ a.asIso.hom.val := by
    have hc : (eqToIso hx).conjAut b = a := (eqToIso hx).conjAut.apply_symm_apply a
    have hm : ((eqToIso hε).conjAut (Functor.Fiber.fiberInclusion.mapAut _ b)).asIso =
        Functor.Fiber.fiberInclusion.mapIso a.asIso := by
      have hm' := congrArg (fun z => Functor.Fiber.fiberInclusion.mapIso z.asIso) hc
      rwa [Functor.map_conjAut, fiberInclusion_mapIso_eqToIso hx hε] at hm'
    have hmhom' : eqToHom hε.symm ≫ b.asIso.hom.val ≫ eqToHom hε = a.asIso.hom.val :=
      congrArg (fun z => z.hom) hm
    simpa [Category.assoc] using congrArg (fun z => eqToHom hε ≫ z) hmhom'
  have hw : b.asIso.hom.val ≫ yε.1.hom = yε.1.hom := by
    rw [hεhom, ← Category.assoc, hb, Category.assoc,
      (mem_infinitesimalAutomorphisms_iff hp.cofibered g e hpair i hi a).mp ha]
  obtain ⟨αQ, hαQ⟩ := exists_objectsOverFiberForget_mapAut_eq yε b hw
  refine ⟨αQ, ?_⟩
  show (eqToIso hx).conjAut (G.mapAut yε αQ) = a
  rw [hαQ]
  simp [b]

/-- Infinitesimal automorphisms of objects over `x₀` are the infinitesimal
automorphisms of `x₀`. -/
@[stacks 06JS "infinitesimal_automorphisms_of_localization"]
public theorem infinitesimalAutomorphismGroup_objectsOverFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₀ : p.Fiber (residueFieldObject Λ k)} {xε : p.Fiber Aε}
    (g : residueFieldObject Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    {y₀ : (objectsOverFunctor p x₀.1).Fiber
      (residueFieldObject Λ k)}
    {yε : (objectsOverFunctor p x₀.1).Fiber Aε}
    (j : y₀.1 ⟶ yε.1)
    (hj : (objectsOverFunctor p x₀.1).IsHomLift g j)
    (h₀ : y₀.1.left = x₀.1) (hε : yε.1.left = xε.1)
    (h₀hom : y₀.1.hom = eqToHom h₀)
    (hεhom : yε.1.hom = eqToHom hε ≫
      (canonicalRetraction hp.cofibered g e hpair.split i hi).1)
    (hjleft : j.left ≫ eqToHom hε = eqToHom h₀ ≫ i) :
    ∃! E :
      infinitesimalAutomorphismGroup
        (isPredeformationCategory_objectsOverFunctor p hp.cofibered x₀)
        g e hpair j hj ≃* infinitesimalAutomorphismGroup hp g e hpair i hi,
      ∀ a, (E a).val.asIso.hom.val =
        eqToHom hε.symm ≫ a.val.asIso.hom.val.left ≫ eqToHom hε := by
  let hpq := isPredeformationCategory_objectsOverFunctor p hp.cofibered x₀
  let G := objectsOverFiberForget p x₀.1 Aε
  have hx : G.obj yε = xε := Subtype.ext hε
  let φ : Aut yε →* Aut xε := (eqToIso hx).conjAut.toMonoidHom.comp (G.mapAut yε)
  have hφ (a : Aut yε) :
      (φ a).asIso.hom.val = eqToHom hε.symm ≫ a.asIso.hom.val.left ≫ eqToHom hε := by
    show (Functor.Fiber.fiberInclusion.mapIso ((eqToIso hx).conjAut (G.mapAut yε a)).asIso).hom = _
    rw [Functor.map_conjAut, fiberInclusion_mapIso_eqToIso hx hε]
    rfl
  let S : Subgroup (Aut xε) := infinitesimalAutomorphisms hp.cofibered g e hpair i hi
  let T : Subgroup (Aut yε) := infinitesimalAutomorphisms hpq.cofibered g e hpair j hj
  have hmem (a : Aut yε) : a ∈ T ↔ φ a ∈ S := by
    rw [mem_infinitesimalAutomorphisms_iff hp.cofibered g e hpair i hi, hφ]
    exact mem_infinitesimalAutomorphisms_objectsOverFunctor_iff hp g e hpair i hi j hj h₀ hε
      h₀hom hεhom hjleft a
  have hφ_injective : Function.Injective φ := fun a b hab =>
    objectsOverFiberForget_mapAut_injective yε ((eqToIso hx).conjAut.injective hab)
  have hmap : T.map φ = S := by
    ext a
    refine ⟨fun ⟨b, hb, hba⟩ => hba ▸ (hmem b).mp hb, fun ha => ?_⟩
    obtain ⟨b, rfl⟩ :=
      exists_conjAut_objectsOverFiberForget_mapAut_eq hp g e hpair i hi hε hεhom a ha
    exact ⟨b, (hmem b).mpr ha, rfl⟩
  let E : T ≃* S := (T.equivMapOfInjective φ hφ_injective).trans (MulEquiv.subgroupCongr hmap)
  have hE (a : T) : (E a).1 = φ a.1 := rfl
  have hEval (a : T) :
      (E a).val.asIso.hom.val = eqToHom hε.symm ≫ a.val.asIso.hom.val.left ≫ eqToHom hε :=
    (congrArg (fun z => z.asIso.hom.val) (hE a)).trans (hφ a.1)
  exact ⟨E, hEval, fun E' hE' => MulEquiv.ext fun a => Subtype.ext <| Aut.ext <| Iso.ext <|
    Functor.Fiber.hom_ext <| (hE' a).trans (hEval a).symm⟩

end

end Deformation

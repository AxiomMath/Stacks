module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctorial
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMapComp

/-!
# The colimit category along an endofunctor is the colimit in `Cat`

Let `F : C ⥤ C` be an endofunctor. Stacks Tag 0EXA defines `colim_F C` as the colimit of the
sequential diagram `C →F C →F ⋯` and describes it in down-to-earth terms: objects the pairs
`(E, n)`, Hom-sets the colimits `colim_N Hom_C(F^{N - n}E, F^{N - m}G)`. The down-to-earth
category is `CategoryTheory.EndoColim F`; the colimit in `Cat` (of the diagram with each copy of
`C` replaced by the equivalent small category `AsSmall C`, as colimits in `Cat` require) is
`CategoryTheory.EndoColim.catColimit F`. This file proves that **the two are equivalent**, by
the functor which is the colimit coprojection at the stage `n` on the stage-`n` copy of `C`.

## Main definitions

* `CategoryTheory.EndoColim.Linked` and `CategoryTheory.EndoColim.link`: two objects `(E, n)`,
  `(G, m)` are linked when `F^{m + k}E = F^{n + k}G` for some `k`, and then the identity of that
  common object presents a canonical isomorphism between them. The stage shift
  `(F E, n + 1) ≅ (E, n)` is one (`CategoryTheory.EndoColim.shiftStepHom_eq_link`).
* `CategoryTheory.EndoColim.Strict`: the strict model, whose objects are the classes of linked
  objects — the pairs `(E, n)` with `(E, n)` identified with `(F E, n + 1)` — and whose
  morphisms are those of `colim_F C` between chosen representatives.
* `CategoryTheory.EndoColim.toCatColimit`: the comparison functor
  `colim_F C ⥤ colim_{Cat}(C →F C →F ⋯)`.

## Main results

* `CategoryTheory.EndoColim.Hom.of_eq_link_comp_stageHomOf`: every morphism of `colim_F C` is a
  stage morphism between linked objects.
* `CategoryTheory.EndoColim.strictEquivalence`: `colim_F C` is equivalent to its strict model.
* `CategoryTheory.EndoColim.strictStage_compat` and
  `CategoryTheory.EndoColim.strict_functor_ext`: the stage functors into the strict model form a
  strict cocone, and functors out of the strict model are determined by their restrictions to
  the stages; that is, the strict model is the colimit in `Cat`.
* `CategoryTheory.EndoColim.isEquivalence_toCatColimit` and
  `CategoryTheory.EndoColim.catColimitEquivalence`: **`colim_F C` is equivalent to the colimit
  of `C →F C →F ⋯` in `Cat`.**
* `CategoryTheory.EndoColim.exists_catStage_obj_eq`: every object of the colimit in `Cat` is the
  image of an object of `C` under a coprojection.

## Implementation notes

A cocone in `Cat` asks for equalities of functors, and the stage functors of `colim_F C` satisfy
`F ⋙ (stage n + 1) ≅ (stage n)` only up to the shift isomorphism, so the comparison goes
through the strict model, where linked objects become equal. The functor from the colimit in
`Cat` to the strict model is induced by the strict cocone of stage functors, the functor back is
the comparison functor restricted along the choice of representatives, and the two composites
are identities by the uniqueness halves of the two universal properties. Uniqueness for the
strict model rests on the decomposition of every morphism as a stage morphism between linked
objects, and on the fact that every functor in sight sends the canonical morphisms between
linked objects to identities (`CategoryTheory.EndoColim.SendsLinksToEqToHom`).

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-! ### Linked objects and the canonical morphisms between them -/

/-- Two objects `(E, n)` and `(G, m)` of `colim_F C` are **linked** when `F^{m + k}E = F^{n + k}G`
for some `k`, that is, when `E` and `G` become the same object at a common level of the
diagram `C →F C →F ⋯`. -/
def Linked (A B : EndoColim F) : Prop :=
  ∃ k : ℕ, (F.endoIter (B.stage + k)).obj A.obj = (F.endoIter (A.stage + k)).obj B.obj

/-- Every object of `colim_F C` is linked to itself. -/
lemma Linked.refl (A : EndoColim F) : Linked A A := ⟨0, rfl⟩

/-- Linking is symmetric. -/
lemma Linked.symm {A B : EndoColim F} (h : Linked A B) : Linked B A :=
  h.imp fun _ ↦ Eq.symm

/-- Iterates of `F` with equal exponents agree. -/
lemma endoIter_obj_congr (E : C) {a b : ℕ} (h : a = b) :
    (F.endoIter a).obj E = (F.endoIter b).obj E := by
  rw [h]

/-- Linking is transitive. -/
lemma Linked.trans {A B D : EndoColim F} (h₁ : Linked A B) (h₂ : Linked B D) : Linked A D := by
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨l, hl⟩ := h₂
  refine ⟨B.stage + k + l, ?_⟩
  refine (endoIter_obj_congr A.obj (by omega)).trans
    ((endoIter_obj_eq_raise hk (D.stage + l)).trans
      ((endoIter_obj_congr B.obj (by omega)).trans
        ((endoIter_obj_eq_raise hl (A.stage + k)).trans
          (endoIter_obj_congr D.obj (by omega)))))

/-- An object and its image under `F` placed one stage higher are linked. -/
lemma linked_shift (E : C) (n : ℕ) : Linked (⟨E, n⟩ : EndoColim F) ⟨F.obj E, n + 1⟩ :=
  ⟨0, (F.endoIter_obj_obj (n + 0) E).symm⟩

/-- **Two presentations by transports of objects present the same morphism**, whatever the
levels. -/
lemma Hom.of_eqToHom_eq {A B : EndoColim F} {k l : ℕ}
    (h : (F.endoIter (B.stage + k)).obj A.obj = (F.endoIter (A.stage + k)).obj B.obj)
    (h' : (F.endoIter (B.stage + l)).obj A.obj = (F.endoIter (A.stage + l)).obj B.obj) :
    Hom.of k (eqToHom h) = Hom.of l (eqToHom h') := by
  refine Hom.of_eq_of _ _ l k (by omega) ?_
  simp only [endoRaise_eqToHom, endoHomCast_eqToHom]

/-- **The canonical morphism between linked objects**: the morphism presented by the identity of
the common value of the two objects at a level where they agree. -/
noncomputable def link {A B : EndoColim F} (h : Linked A B) : A ⟶ B :=
  Hom.of h.choose (eqToHom h.choose_spec)

/-- The canonical morphism between linked objects is presented by the identity of their common
value at any level `k` where they agree. -/
lemma link_eq_of {A B : EndoColim F} (h : Linked A B) (k : ℕ)
    (hk : (F.endoIter (B.stage + k)).obj A.obj = (F.endoIter (A.stage + k)).obj B.obj) :
    link h = Hom.of k (eqToHom hk) :=
  Hom.of_eqToHom_eq _ _

/-- The canonical morphism from an object to itself is the identity. -/
@[simp]
lemma link_self {A : EndoColim F} (h : Linked A A) : link h = 𝟙 A :=
  link_eq_of h 0 rfl

/-- The composite of two canonical morphisms between linked objects is the canonical morphism. -/
@[reassoc (attr := simp)]
lemma link_comp_link {A B D : EndoColim F} (h₁ : Linked A B) (h₂ : Linked B D) :
    link h₁ ≫ link h₂ = link (h₁.trans h₂) := by
  obtain ⟨k, hk⟩ := id h₁
  obtain ⟨l, hl⟩ := id h₂
  rw [link_eq_of h₁ k hk, link_eq_of h₂ l hl]
  show Hom.of (B.stage + k + l) (compHom k (eqToHom hk) l (eqToHom hl)) = _
  simp only [compHom, endoRaise_eqToHom, endoHomCast_eqToHom, eqToHom_trans]
  exact (link_eq_of _ _ _).symm

/-- The transport morphism along an equality of objects is the canonical morphism. -/
lemma eqToHom_eq_link {A B : EndoColim F} (e : A = B) :
    eqToHom e = link (e ▸ Linked.refl A) := by
  subst e
  exact (link_self _).symm

/-- The canonical isomorphism between linked objects. -/
@[simps]
noncomputable def linkIso {A B : EndoColim F} (h : Linked A B) : A ≅ B where
  hom := link h
  inv := link h.symm
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The stage shift `(F E, n + 1) ⟶ (E, n)` is the canonical morphism. -/
lemma shiftStepHom_eq_link (E : C) (n : ℕ) :
    shiftStepHom F n E = link (linked_shift E n).symm :=
  (link_eq_of _ 0 _).symm

/-- The inverse stage shift `(E, n) ⟶ (F E, n + 1)` is the canonical morphism. -/
lemma shiftStepInv_eq_link (E : C) (n : ℕ) :
    shiftStepInv F n E = link (linked_shift E n) :=
  (link_eq_of _ 0 _).symm

/-! ### Every morphism is a stage morphism between linked objects -/

/-- The object `(F^{m + k}E, n + m + k)`, the source of the stage morphism decomposing a morphism
`(E, n) ⟶ (G, m)` presented at level `k`. -/
abbrev decompSource (A B : EndoColim F) (k : ℕ) : EndoColim F :=
  ⟨(F.endoIter (B.stage + k)).obj A.obj, A.stage + B.stage + k⟩

/-- The object `(F^{n + k}G, n + m + k)`, the target of the stage morphism decomposing a morphism
`(E, n) ⟶ (G, m)` presented at level `k`. -/
abbrev decompTarget (A B : EndoColim F) (k : ℕ) : EndoColim F :=
  ⟨(F.endoIter (A.stage + k)).obj B.obj, A.stage + B.stage + k⟩

/-- The witness at level `0` that `A` is linked to `decompSource A B k`. -/
private lemma decompSource_eq (A B : EndoColim F) (k : ℕ) :
    (F.endoIter ((decompSource A B k).stage + 0)).obj A.obj =
      (F.endoIter (A.stage + 0)).obj (decompSource A B k).obj :=
  (endoIter_obj_endoIter_obj_of_eq F (N := A.stage + 0) (a := B.stage + k)
    (b := A.stage + B.stage + k + 0) (by omega) A.obj).symm

/-- The witness at level `0` that `decompTarget A B k` is linked to `B`. -/
private lemma decompTarget_eq (A B : EndoColim F) (k : ℕ) :
    (F.endoIter (B.stage + 0)).obj (decompTarget A B k).obj =
      (F.endoIter ((decompTarget A B k).stage + 0)).obj B.obj :=
  endoIter_obj_endoIter_obj_of_eq F (N := B.stage + 0) (a := A.stage + k)
    (b := A.stage + B.stage + k + 0) (by omega) B.obj

/-- An object `A` is linked to the source `decompSource A B k` of the stage morphism
decomposing a morphism `A ⟶ B` presented at level `k`. -/
lemma linked_decompSource (A B : EndoColim F) (k : ℕ) : Linked A (decompSource A B k) :=
  ⟨0, decompSource_eq A B k⟩

/-- The target `decompTarget A B k` of the stage morphism decomposing a morphism `A ⟶ B`
presented at level `k` is linked to `B`. -/
lemma linked_decompTarget (A B : EndoColim F) (k : ℕ) : Linked (decompTarget A B k) B :=
  ⟨0, decompTarget_eq A B k⟩

/-- **Every morphism of `colim_F C` is a stage morphism between linked objects.** The morphism
`(E, n) ⟶ (G, m)` presented at level `k` by `f : F^{m + k}E ⟶ F^{n + k}G` is the canonical
morphism `(E, n) ⟶ (F^{m + k}E, N)`, followed by the stage-`N` image of `f`, followed by the
canonical morphism `(F^{n + k}G, N) ⟶ (G, m)`, where `N = n + m + k`. -/
lemma Hom.of_eq_link_comp_stageHomOf {A B : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) :
    Hom.of k f = link (linked_decompSource A B k) ≫
      stageHomOf F (A.stage + B.stage + k) f ≫ link (linked_decompTarget A B k) := by
  rw [link_eq_of _ 0 (decompSource_eq A B k), link_eq_of _ 0 (decompTarget_eq A B k), stageHomOf]
  show _ = Hom.of ((A.stage + B.stage + k) + 0 + ((A.stage + B.stage + k) + 0 + 0)) _
  refine (Hom.of_eq_of _ _ 0 (2 * A.stage + 2 * B.stage + k) (by omega) ?_).symm
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoHomCast,
    endoRaise_eqToHom, endoRaise_endoIter_map, endoHomCast_comp_rfl, endoHomCast_endoHomCast,
    endoHomCast_eqToHom]
  exact eqToHom_comp_endoIter_map_comp_eqToHom_eq' F f (by omega) (by omega) (by omega)
    (by omega) (by omega) _ _

/-! ### Functors sending the canonical morphisms to identities -/

section Links

variable {D : Type*} [Category D]

/-- A functor out of `colim_F C` **sends links to identities** when it identifies the two ends of
every canonical morphism between linked objects and sends that morphism to the identity. -/
def SendsLinksToEqToHom (M : EndoColim F ⥤ D) : Prop :=
  ∀ (A B : EndoColim F) (h : Linked A B), ∃ e : M.obj A = M.obj B, M.map (link h) = eqToHom e

/-- **A functor out of `colim_F C` sending links to identities is determined by its restrictions
to the stages**, as a functor: every morphism of `colim_F C` is a stage morphism between linked
objects. -/
lemma functor_ext_of_stage {M M' : EndoColim F ⥤ D} (hM : SendsLinksToEqToHom M)
    (hM' : SendsLinksToEqToHom M') (h : ∀ n, stageFunctor F n ⋙ M = stageFunctor F n ⋙ M') :
    M = M' := by
  have hobj : ∀ A : EndoColim F, M.obj A = M'.obj A := fun A ↦ Functor.congr_obj (h A.stage) A.obj
  refine Functor.ext hobj (fun A B u ↦ ?_)
  obtain ⟨k, f, rfl⟩ := Hom.exists_of (u : Hom A B)
  rw [Hom.of_eq_link_comp_stageHomOf]
  obtain ⟨e₁, he₁⟩ := hM _ _ (linked_decompSource A B k)
  obtain ⟨e₂, he₂⟩ := hM _ _ (linked_decompTarget A B k)
  obtain ⟨e₁', he₁'⟩ := hM' _ _ (linked_decompSource A B k)
  obtain ⟨e₂', he₂'⟩ := hM' _ _ (linked_decompTarget A B k)
  have hf : M.map (stageHomOf F (A.stage + B.stage + k) f) = eqToHom (hobj _) ≫
      M'.map (stageHomOf F (A.stage + B.stage + k) f) ≫ eqToHom (hobj _).symm :=
    Functor.congr_hom (h (A.stage + B.stage + k)) f
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, he₁, he₂, he₁',
    he₂', hf]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end Links

/-! ### The strict model -/

variable (F) in
/-- The setoid of linked objects of `colim_F C`. -/
def linkedSetoid : _root_.Setoid (EndoColim F) where
  r := Linked
  iseqv := ⟨Linked.refl, Linked.symm, Linked.trans⟩

variable (F) in
/-- **The objects of the strict colimit**: the objects of `colim_F C` up to linking, that is the
pairs `(E, n)` with `(E, n)` identified with `(F E, n + 1)`. -/
abbrev StrictObj : Type u := _root_.Quotient (linkedSetoid F)

/-- The class of an object of `colim_F C` among the objects of the strict colimit. -/
def StrictObj.mk (A : EndoColim F) : StrictObj F := _root_.Quotient.mk _ A

/-- Linked objects have the same class. -/
lemma StrictObj.mk_eq_mk {A B : EndoColim F} (h : Linked A B) :
    StrictObj.mk A = StrictObj.mk B :=
  _root_.Quotient.sound h

/-- The class of the chosen representative of a class is that class. -/
lemma StrictObj.mk_out (q : StrictObj F) : StrictObj.mk (_root_.Quotient.out q) = q :=
  _root_.Quotient.out_eq q

/-- The chosen representative of the class of an object is linked to that object. -/
lemma linked_out_mk (A : EndoColim F) : Linked (_root_.Quotient.out (StrictObj.mk A)) A :=
  _root_.Quotient.mk_out (s := linkedSetoid F) A

/-- The chosen representatives of equal classes are linked. -/
lemma linked_out_of_eq {q q' : StrictObj F} (e : q = q') :
    Linked (_root_.Quotient.out q) (_root_.Quotient.out q') :=
  e ▸ Linked.refl _

variable (F) in
/-- **The strict colimit of `C →F C →F ⋯`**: its objects are the classes of linked objects of
`colim_F C`, and its morphisms are the morphisms of `colim_F C` between chosen representatives.
-/
noncomputable abbrev Strict : Type u :=
  InducedCategory (EndoColim F) (fun q : StrictObj F ↦ _root_.Quotient.out q)

/-- The functor picking the chosen representative of a class. -/
noncomputable abbrev strictOut : Strict F ⥤ EndoColim F :=
  inducedFunctor (fun q : StrictObj F ↦ _root_.Quotient.out q)

/-- The chosen representatives of equal objects of the strict colimit are linked. -/
lemma linked_strictOut_of_eq {q q' : Strict F} (e : q = q') :
    Linked ((strictOut (F := F)).obj q) ((strictOut (F := F)).obj q') :=
  e ▸ Linked.refl _

/-- An identity of the strict colimit is the canonical morphism between the representatives. -/
lemma strict_eqToHom_hom {q q' : Strict F} (e : q = q') :
    (strictOut (F := F)).map (eqToHom e) = link (linked_strictOut_of_eq e) := by
  subst e
  simp

variable (F) in
/-- The functor `colim_F C ⥤ Strict` taking an object to its class. It is an equivalence, whose
inverse picks representatives. -/
noncomputable def toStrict : EndoColim F ⥤ Strict F where
  obj A := StrictObj.mk A
  map {A B} u := InducedCategory.homMk (link (linked_out_mk A) ≫ u ≫ link (linked_out_mk B).symm)
  map_id A := InducedCategory.hom_ext (show link _ ≫ 𝟙 A ≫ link _ = 𝟙 _ by simp)
  map_comp {A B D} u v := InducedCategory.hom_ext
    (show link _ ≫ (u ≫ v) ≫ link _ = (link _ ≫ u ≫ link _) ≫ (link _ ≫ v ≫ link _) by simp)

/-- The chosen representative of the class of an object `A` is linked to `A`. -/
lemma linked_strictOut_toStrict (A : EndoColim F) :
    Linked ((strictOut (F := F)).obj ((toStrict F).obj A)) A :=
  linked_out_mk A

/-- The class functor identifies linked objects. -/
lemma toStrict_obj_eq {A B : EndoColim F} (h : Linked A B) :
    (toStrict F).obj A = (toStrict F).obj B :=
  StrictObj.mk_eq_mk h

/-- The class of the chosen representative of an object `q` of the strict colimit is `q`. -/
lemma toStrict_obj_strictOut_obj (q : Strict F) :
    (toStrict F).obj ((strictOut (F := F)).obj q) = q :=
  StrictObj.mk_out q

/-- The class functor on a morphism `u : A ⟶ B`, read on the chosen representatives, is `u`
conjugated by the canonical morphisms between the representatives and `A`, `B`. -/
lemma toStrict_map_hom {A B : EndoColim F} (u : A ⟶ B) :
    (strictOut (F := F)).map ((toStrict F).map u) =
      link (linked_strictOut_toStrict A) ≫ u ≫ link (linked_strictOut_toStrict B).symm :=
  rfl

/-- **The class functor sends links to identities.** -/
lemma toStrict_map_link {A B : EndoColim F} (h : Linked A B) :
    (toStrict F).map (link h) = eqToHom (toStrict_obj_eq h) := by
  refine (strictOut (F := F)).map_injective ?_
  rw [toStrict_map_hom, link_comp_link, link_comp_link]
  exact (strict_eqToHom_hom _).symm

/-- The class functor followed by any functor out of the strict colimit sends links to
identities. -/
lemma sendsLinksToEqToHom_toStrict_comp {D : Type*} [Category D] (K : Strict F ⥤ D) :
    SendsLinksToEqToHom (toStrict F ⋙ K) :=
  fun _ _ h ↦ ⟨_, by rw [Functor.comp_map, toStrict_map_link, eqToHom_map]⟩

/-- Picking representatives and then taking classes is the identity of the strict colimit. -/
lemma strictOut_comp_toStrict : strictOut (F := F) ⋙ toStrict F = 𝟭 (Strict F) := by
  refine Functor.ext toStrict_obj_strictOut_obj (fun q q' u ↦ ?_)
  refine (strictOut (F := F)).map_injective ?_
  rw [Functor.comp_map, toStrict_map_hom, Functor.map_comp, Functor.map_comp,
    strict_eqToHom_hom, strict_eqToHom_hom, Functor.id_map]

/-- Taking classes and then picking representatives does not change a functor which sends links
to identities. -/
lemma toStrict_comp_strictOut_comp {D : Type*} [Category D] (M : EndoColim F ⥤ D)
    (hM : SendsLinksToEqToHom M) :
    toStrict F ⋙ strictOut (F := F) ⋙ M = M := by
  refine Functor.ext (fun A ↦ (hM _ _ (linked_strictOut_toStrict A)).choose) (fun A B u ↦ ?_)
  obtain ⟨e₁, he₁⟩ := hM _ _ (linked_strictOut_toStrict A)
  obtain ⟨e₂, he₂⟩ := hM B ((strictOut (F := F)).obj ((toStrict F).obj B))
    (linked_strictOut_toStrict B).symm
  rw [Functor.comp_map, Functor.comp_map, toStrict_map_hom]
  simp only [Functor.map_comp, he₁, he₂]

variable (F) in
/-- **`colim_F C` is equivalent to its strict model.** -/
noncomputable def strictEquivalence : EndoColim F ≌ Strict F :=
  Equivalence.mk (toStrict F) strictOut
    (NatIso.ofComponents (fun A ↦ linkIso (linked_strictOut_toStrict A).symm) (fun {A B} u ↦ by
      rw [Functor.comp_map, toStrict_map_hom]
      simp))
    (eqToIso strictOut_comp_toStrict)

/-- The class functor `colim_F C ⥤ Strict` is an equivalence. -/
instance : (toStrict F).IsEquivalence :=
  (strictEquivalence F).isEquivalence_functor

/-! ### The strict cocone -/

variable (F) in
/-- The stage-`n` functor `C ⥤ Strict` into the strict colimit. -/
noncomputable def strictStage (n : ℕ) : C ⥤ Strict F :=
  stageFunctor F n ⋙ toStrict F

/-- **The stage functors into the strict colimit form a strict cocone**: pulling back along `F`
and placing at the stage `n + 1` is placing at the stage `n`, as an equality of functors. -/
lemma strictStage_compat (n : ℕ) : F ⋙ strictStage F (n + 1) = strictStage F n := by
  refine Functor.ext (fun E ↦ toStrict_obj_eq (linked_shift E n).symm) (fun E G g ↦ ?_)
  have hnat := shiftStepHom_naturality' F n g
  rw [shiftStepHom_eq_link, shiftStepHom_eq_link] at hnat
  have key : stageHomOf F (n + 1) (F.map g) =
      link (linked_shift E n).symm ≫ stageHomOf F n g ≫ link (linked_shift G n) := by
    rw [← Category.assoc, ← hnat, Category.assoc, link_comp_link, link_self, Category.comp_id]
  show (toStrict F).map (stageHomOf F (n + 1) (F.map g)) =
    _ ≫ (toStrict F).map (stageHomOf F n g) ≫ _
  rw [key, Functor.map_comp, Functor.map_comp, toStrict_map_link, toStrict_map_link]
  rfl

/-- **Functors out of the strict colimit are determined by their restrictions to the stages.** -/
lemma strict_functor_ext {D : Type*} [Category D] {K K' : Strict F ⥤ D}
    (h : ∀ n, strictStage F n ⋙ K = strictStage F n ⋙ K') : K = K' := by
  have h' : toStrict F ⋙ K = toStrict F ⋙ K' :=
    functor_ext_of_stage (sendsLinksToEqToHom_toStrict_comp K)
      (sendsLinksToEqToHom_toStrict_comp K') h
  have e (K : Strict F ⥤ D) : (strictOut (F := F) ⋙ toStrict F) ⋙ K = K := by
    rw [strictOut_comp_toStrict]; rfl
  rw [← e K, ← e K', Functor.assoc, Functor.assoc, h']

/-! ### Strict pseudo-cocones -/

section OfStrict

variable {D : Type*} [Category D] (G : ℕ → C ⥤ D) (hG : ∀ n, F ⋙ G (n + 1) = G n)

/-- The pseudo-cocone of a strict cocone, whose comparisons are identities. -/
abbrev Pseudococone.ofStrict : Pseudococone F D where
  stage := G
  compat n := eqToIso (hG n)

include hG in
/-- For a strict cocone `G`, placing `F^k X` at the stage `n + k` is placing `X` at the stage
`n`. -/
lemma stage_endoIter_obj (n : ℕ) : ∀ (k : ℕ) (X : C),
    (G (n + k)).obj ((F.endoIter k).obj X) = (G n).obj X
  | 0, _ => rfl
  | k + 1, X => (Functor.congr_obj (hG (n + k)) _).trans (stage_endoIter_obj n k X)

/-- The iterated comparison isomorphism of the pseudo-cocone of a strict cocone is the transport
along `stage_endoIter_obj`. -/
lemma ofStrict_iterObjIso_hom (n : ℕ) : ∀ (k : ℕ) (X : C),
    ((Pseudococone.ofStrict G hG).iterObjIso n k X).hom =
      eqToHom (stage_endoIter_obj G hG n k X)
  | 0, _ => rfl
  | k + 1, X => by
      rw [Pseudococone.iterObjIso_succ_hom, ofStrict_iterObjIso_hom n k X]
      simp [Pseudococone.compatIter, Pseudococone.ofStrict, eqToHom_app]

/-- The inverse of the iterated comparison isomorphism of the pseudo-cocone of a strict cocone is
the transport along `stage_endoIter_obj`. -/
lemma ofStrict_iterObjIso_inv (n k : ℕ) (X : C) :
    ((Pseudococone.ofStrict G hG).iterObjIso n k X).inv =
      eqToHom (stage_endoIter_obj G hG n k X).symm := by
  refine Iso.inv_ext ?_
  rw [ofStrict_iterObjIso_hom]
  simp

/-- **The functor out of `colim_F C` determined by a strict cocone sends links to
identities.** -/
lemma sendsLinksToEqToHom_ofStrict_desc :
    SendsLinksToEqToHom (Pseudococone.ofStrict G hG).desc := by
  intro A B hl
  obtain ⟨k, hk⟩ := id hl
  have e : (G A.stage).obj A.obj = (G B.stage).obj B.obj :=
    (stage_endoIter_obj G hG A.stage (B.stage + k) A.obj).symm.trans
      ((congrArg (fun t ↦ (G t).obj ((F.endoIter (B.stage + k)).obj A.obj))
        (show A.stage + (B.stage + k) = B.stage + (A.stage + k) by omega)).trans
        ((congrArg (G (B.stage + (A.stage + k))).obj hk).trans
          (stage_endoIter_obj G hG B.stage (A.stage + k) B.obj)))
  refine ⟨e, ?_⟩
  rw [link_eq_of hl k hk, Pseudococone.desc_map, Pseudococone.homMap_of,
    Pseudococone.mapRep, Pseudococone.mapAt, ofStrict_iterObjIso_inv, ofStrict_iterObjIso_hom,
    eqToHom_map]
  simp only [Pseudococone.stageHom, eqToHom_app, eqToHom_trans]
  rfl

end OfStrict

/-! ### The colimit in `Cat` -/

section Cat

variable (F)

/-- The sequential diagram `C →F C →F ⋯` in the category of small categories, each copy of `C`
being replaced by the equivalent small category `AsSmall C`. -/
noncomputable abbrev catDiagram : ℕ ⥤ Cat.{max w v u, max w v u} :=
  endoSequence (Cat.asSmallFunctor.{w, v, u}.map F.toCatHom)

/-- The colimit of `C →F C →F ⋯` in `Cat`. -/
noncomputable abbrev catColimit : Cat.{max w v u, max w v u} :=
  colimit (catDiagram.{w} F)

/-- The colimit leg at the stage `n`, as a functor out of `C`. -/
noncomputable def catStage (n : ℕ) : C ⥤ catColimit.{w} F :=
  AsSmall.up ⋙ (endoColimitι (Cat.asSmallFunctor.{w, v, u}.map F.toCatHom) n).toFunctor

/-- The colimit legs form a strict cocone. -/
lemma catStage_compat (n : ℕ) : F ⋙ catStage.{w} F (n + 1) = catStage.{w} F n :=
  congrArg (fun K ↦ AsSmall.up ⋙ K)
    (congrArg Cat.Hom.toFunctor
      (comp_endoColimitι_succ (Cat.asSmallFunctor.{w, v, u}.map F.toCatHom) n))

/-- **The comparison functor from the colimit category `colim_F C` of Stacks Tag 0EXA to the
colimit of `C →F C →F ⋯` in `Cat`**: on the stage-`n` copy of `C` it is the colimit leg at the
stage `n`. -/
noncomputable def toCatColimit : EndoColim F ⥤ catColimit.{w} F :=
  (Pseudococone.ofStrict (catStage.{w} F) (catStage_compat.{w} F)).desc

/-- **The comparison functor places an object of `C` at the stage `n` exactly as the colimit leg
does**: the object `(E, n)` of `colim_F C` goes to the image of `E` under the stage-`n` leg. -/
lemma stageFunctor_comp_toCatColimit (n : ℕ) :
    stageFunctor F n ⋙ toCatColimit.{w} F = catStage.{w} F n :=
  (Pseudococone.ofStrict (catStage.{w} F) (catStage_compat.{w} F)).stageFunctor_comp_desc n

/-- The functor from the strict model to the colimit in `Cat`. -/
noncomputable def strictToCatColimit : Strict F ⥤ catColimit.{w} F :=
  strictOut ⋙ toCatColimit.{w} F

/-- The class functor followed by the functor from the strict model to the colimit in `Cat` is
the comparison functor `toCatColimit`. -/
lemma toStrict_comp_strictToCatColimit :
    toStrict F ⋙ strictToCatColimit.{w} F = toCatColimit.{w} F :=
  toStrict_comp_strictOut_comp _
    (sendsLinksToEqToHom_ofStrict_desc (catStage.{w} F) (catStage_compat.{w} F))

/-- The stage-`n` functor into the strict model followed by the functor to the colimit in `Cat`
is the colimit leg at the stage `n`. -/
lemma strictStage_comp_strictToCatColimit (n : ℕ) :
    strictStage F n ⋙ strictToCatColimit.{w} F = catStage.{w} F n := by
  rw [strictStage, Functor.assoc, toStrict_comp_strictToCatColimit,
    stageFunctor_comp_toCatColimit]

/-- The leg at the stage `n` of the strict cocone with summit the strict model. -/
noncomputable def strictLeg (n : ℕ) :
    (catDiagram.{w} F).obj n ⟶ Cat.of (AsSmall.{w} (Strict F)) :=
  (AsSmall.down ⋙ strictStage F n ⋙ AsSmall.up).toCatHom

/-- The legs into the strict model form a strict cocone over `C →F C →F ⋯` in `Cat`. -/
lemma strictLeg_compat (n : ℕ) :
    Cat.asSmallFunctor.{w, v, u}.map F.toCatHom ≫ strictLeg.{w} F (n + 1) = strictLeg.{w} F n :=
  congrArg (fun K ↦ (AsSmall.down ⋙ K ⋙ AsSmall.up).toCatHom) (strictStage_compat n)

/-- The functor from the colimit in `Cat` to the strict model, induced by the strict cocone of
stage functors. -/
noncomputable def catColimitToStrict : catColimit.{w} F ⥤ Strict F :=
  (endoColimitDesc (Cat.asSmallFunctor.{w, v, u}.map F.toCatHom) (strictLeg.{w} F)
    (strictLeg_compat.{w} F)).toFunctor ⋙ AsSmall.down

/-- The colimit leg at the stage `n` followed by the functor to the strict model is the stage-`n`
functor into the strict model. -/
lemma catStage_comp_catColimitToStrict (n : ℕ) :
    catStage.{w} F n ⋙ catColimitToStrict.{w} F = strictStage F n :=
  congrArg (fun K ↦ AsSmall.up ⋙ K ⋙ AsSmall.down)
    (congrArg Cat.Hom.toFunctor
      (endoColimitι_comp_endoColimitDesc (Cat.asSmallFunctor.{w, v, u}.map F.toCatHom)
        (strictLeg.{w} F) (strictLeg_compat.{w} F) n))

/-- The functor from the colimit in `Cat` to the strict model and back is the identity. -/
lemma catColimitToStrict_comp_strictToCatColimit :
    catColimitToStrict.{w} F ⋙ strictToCatColimit.{w} F = 𝟭 _ := by
  have h : (catColimitToStrict.{w} F ⋙ strictToCatColimit.{w} F).toCatHom = 𝟙 _ :=
    endoColimit_hom_ext (Cat.asSmallFunctor.{w, v, u}.map F.toCatHom) (fun n ↦ by
      refine Cat.ext ?_
      show AsSmall.down ⋙ (catStage.{w} F n ⋙ catColimitToStrict.{w} F) ⋙
          strictToCatColimit.{w} F = AsSmall.down ⋙ catStage.{w} F n
      rw [catStage_comp_catColimitToStrict, strictStage_comp_strictToCatColimit])
  exact congrArg Cat.Hom.toFunctor h

/-- The functor from the strict model to the colimit in `Cat` and back is the identity. -/
lemma strictToCatColimit_comp_catColimitToStrict :
    strictToCatColimit.{w} F ⋙ catColimitToStrict.{w} F = 𝟭 _ :=
  strict_functor_ext (fun n ↦ by
    rw [← Functor.assoc, strictStage_comp_strictToCatColimit, catStage_comp_catColimitToStrict]
    rfl)

/-- The functor from the strict model to the colimit in `Cat` is an equivalence. -/
instance : (strictToCatColimit.{w} F).IsEquivalence :=
  (Equivalence.mk (strictToCatColimit.{w} F) (catColimitToStrict.{w} F)
    (eqToIso (strictToCatColimit_comp_catColimitToStrict.{w} F).symm)
    (eqToIso (catColimitToStrict_comp_strictToCatColimit.{w} F))).isEquivalence_functor

/-- **The comparison functor from the colimit category `colim_F C` of Stacks Tag 0EXA to the
colimit of `C →F C →F ⋯` in `Cat` is an equivalence.** -/
instance isEquivalence_toCatColimit : (toCatColimit.{w} F).IsEquivalence := by
  rw [← toStrict_comp_strictToCatColimit]
  infer_instance

/-- **The colimit category `colim_F C` of Stacks Tag 0EXA is equivalent to the colimit of
`C →F C →F ⋯` in `Cat`**, through the comparison functor which is the colimit leg at the stage
`n` on the stage-`n` copy of `C`. -/
noncomputable def catColimitEquivalence : EndoColim F ≌ catColimit.{w} F :=
  (toCatColimit.{w} F).asEquivalence

/-- **Every object of the colimit of `C →F C →F ⋯` in `Cat` is the image of an object of `C`
under a colimit leg**: it is a pair `(E, n)`. -/
theorem exists_catStage_obj_eq (X : catColimit.{w} F) :
    ∃ (n : ℕ) (E : C), (catStage.{w} F n).obj E = X :=
  ⟨_, _, Functor.congr_obj (catColimitToStrict_comp_strictToCatColimit.{w} F) X⟩

end Cat

end CategoryTheory.EndoColim

end

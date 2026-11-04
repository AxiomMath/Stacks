module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# Faithfulness, full faithfulness and equivalence are fibrewise conditions (Stacks 003Z)

Let `C` be a category and let `p : S ⥤ C`, `p' : S' ⥤ C` be functors fibred in groupoids
(`CategoryTheory.Functor.IsFiberedInGroupoids`, Stacks 003S).  A *functor over `C`* is a
functor `G : S ⥤ S'` with `G ⋙ p' = p`.  Such a `G` restricts, for every object `U` of `C`,
to a functor `G_U : S_U ⥤ S'_U` between the fibre categories; here the fibre `S_U` is
Mathlib's `Functor.Fiber p U`, whose objects are the objects of `S` lying over `U` and whose
morphisms are the morphisms of `S` lying over `𝟙 U`, and the restriction of `G` is
`Fiber.mapOfComp`.

Part (1) of Lemma 4.35.9 says that each of the three properties "faithful", "fully
faithful" and "equivalence of categories" holds for `G` if and only if it holds for every
`G_U`; the three clauses are stated separately below.  The substantial directions are those
descending from the fibres to `S`: faithfulness and fullness descend because the lifting
and unique-factorization axioms let every morphism of `S` be factored as a morphism inside
a fibre followed by a chosen lift of its image in `C`, while essential surjectivity is moved
into a fibre by `IsFiberedInGroupoids.exists_iso_lift`, which promotes an isomorphism of `C` to an
isomorphism of `S` lying over it.

Part (2) upgrades an equivalence of categories to an equivalence in the 2-category of
categories fibred in groupoids over `C`: the quasi-inverse can be chosen to be again a
functor over `C`, with both natural isomorphisms having all their components over identity
morphisms of `C`.  It is built objectwise from `quasiInverse_choice`, which uses part (1) to
choose, for each object `x'` of `S'`, an object `o` of `S` over the same base together with
an isomorphism `x' ≅ G.obj o` lying over an identity; full faithfulness of `G` then
determines the morphism map of the quasi-inverse, and the two natural isomorphisms are
assembled with `NatIso.ofComponents`.

The proofs use `CategoryTheory.Equivalence.essSurj_functor` (Stacks 02C3) and
`CategoryTheory.Functor.IsEquivalence.mk` (Stacks 05SG).
-/

@[expose] public section

-- The fibre inclusion and the induced fibre functor are semireducible, so the endpoints of the
-- composites below agree only once they unfold; relaxing the transparency restriction is what lets
-- `rw`, `simp` and instance search see through them.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {S' : Type u₃} [Category.{v₃} S']

/-- The functor induced on fibres by a functor `G : S ⥤ S'` over `C`, i.e. one satisfying
`G ⋙ p' = p`.  It sends an object `x` lying over `U` to `G x`, which lies over `U` because
`p' (G x) = p x = U`, and a morphism over `𝟙 U` to its image under `G`. -/
def Fiber.mapOfComp (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S') (hG : G ⋙ p' = p) (U : C) :
    p.Fiber U ⥤ p'.Fiber U :=
  Fiber.inducedFunctor (F := Fiber.fiberInclusion ⋙ G) (by
    rw [Functor.assoc, hG]
    exact Fiber.fiberInclusion_comp_eq_const)

/-- The induced fibre functor composed with the fibre inclusion equals the fibre inclusion
composed with `G`. -/
theorem Fiber.mapOfComp_comp_fiberInclusion (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (hG : G ⋙ p' = p) (U : C) :
    (Fiber.mapOfComp p p' G hG U) ⋙ Fiber.fiberInclusion = Fiber.fiberInclusion ⋙ G :=
  Functor.toPrefunctor_injective rfl

/-- On objects the induced fibre functor is `G`. -/
theorem Fiber.fiberInclusion_obj_mapOfComp_obj (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (hG : G ⋙ p' = p) (U : C) (a : p.Fiber U) :
    Fiber.fiberInclusion.obj ((Fiber.mapOfComp p p' G hG U).obj a)
      = G.obj (Fiber.fiberInclusion.obj a) :=
  rfl

/-- On morphisms the induced fibre functor is `G`. -/
theorem Fiber.fiberInclusion_map_mapOfComp_map (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (hG : G ⋙ p' = p) (U : C) {a b : p.Fiber U} (φ : a ⟶ b) :
    Fiber.fiberInclusion.map ((Fiber.mapOfComp p p' G hG U).map φ)
      = G.map (Fiber.fiberInclusion.map φ) :=
  rfl

-- `CategoryTheory.Functor.Fiber.isoMk`, in the module
-- `StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso`, has the same content; that module is
-- not imported here, and a second public declaration of the name would clash in any file importing
-- both, so this copy is private.
/-- An isomorphism of `S` lying over the identity of `U`, read as an isomorphism of the fibre
`p.Fiber U`. This is `Fiber.homMk` for isomorphisms. -/
private def fiberIsoOfIsoOverId (p : S ⥤ C) (U : C) {a b : S} (φ : a ≅ b)
    [p.IsHomLift (𝟙 U) φ.hom] :
    Fiber.mk (IsHomLift.domain_eq p (𝟙 U) φ.hom) ≅
      Fiber.mk (IsHomLift.codomain_eq p (𝟙 U) φ.hom) where
  hom := Fiber.homMk p U φ.hom
  inv := Fiber.homMk p U φ.inv
  hom_inv_id := Fiber.hom_ext (by simp)
  inv_hom_id := Fiber.hom_ext (by simp)

/-- `p.map φ = p'.map (G.map φ)` for any morphism `φ` of `S`, using `G ⋙ p' = p`. -/
theorem map_eq_of_comp_eq (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S') (hG : G ⋙ p' = p)
    {a b : S} (φ : a ⟶ b) :
    p.map φ = eqToHom (by rw [← hG]; rfl) ≫ p'.map (G.map φ) ≫ eqToHom (by rw [← hG]; rfl) := by
  subst hG
  simp

/-- A functor over `C` neither creates nor destroys the property of lying over a morphism of `C`:
`φ` lies over `f` if and only if `G φ` does. -/
theorem isHomLift_map_iff_of_comp_eq (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S') (hG : G ⋙ p' = p)
    {R T : C} (f : R ⟶ T) {a b : S} (φ : a ⟶ b) :
    p'.IsHomLift f (G.map φ) ↔ p.IsHomLift f φ := by
  subst hG
  constructor <;> rintro ⟨⟩ <;> exact .map _

/-- If `G` is faithful then so is each induced fibre functor. -/
private theorem faithful_forall_fiber_of_faithful (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (hG : G ⋙ p' = p) [G.Faithful] (U : C) :
    (Fiber.mapOfComp p p' G hG U).Faithful :=
  Functor.Faithful.of_comp_eq (Fiber.mapOfComp_comp_fiberInclusion p p' G hG U)

/-- If the functor induced on the fibre over `U` is faithful, then `G` is injective on the
morphisms of `S` lying over the identity of `U`. -/
theorem map_injective_of_fiber_faithful (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S') (hG : G ⋙ p' = p)
    (U : C) (hfib : (Fiber.mapOfComp p p' G hG U).Faithful) {a b : S} (α β : a ⟶ b)
    [p.IsHomLift (𝟙 U) α] [p.IsHomLift (𝟙 U) β] (h : G.map α = G.map β) : α = β :=
  congrArg Fiber.fiberInclusion.map
    (hfib.map_injective (a₁ := Fiber.homMk p U α) (a₂ := Fiber.homMk p U β) (Fiber.hom_ext h))

/-- In a category fibred in groupoids, every morphism `g` of the base into `p y` is the base
image of a morphism `χ` into `y`, up to the `eqToHom` comparing the domains. -/
private theorem exists_eqToHom_comp_map_eq {p : S ⥤ C} (hp : p.IsFiberedInGroupoids) {y : S}
    {R : C} (g : R ⟶ p.obj y) :
    ∃ (w : S) (χ : w ⟶ y) (hw : p.obj w = R), eqToHom hw.symm ≫ p.map χ = g := by
  obtain ⟨w, χ, hχ⟩ := hp.exists_lift g y rfl
  exact ⟨w, χ, IsHomLift.domain_eq p g χ, by simp [IsHomLift.fac' p g χ]⟩

/-- If each induced fibre functor is faithful then so is `G`.  Every morphism of `S` factors as a
morphism lying over an identity followed by a chosen lift, and the fibre hypothesis applies to
the first factor. -/
private theorem faithful_of_forall_fiber (p : S ⥤ C) (p' : S' ⥤ C) (hp : p.IsFiberedInGroupoids)
    (hp' : p'.IsFiberedInGroupoids) (G : S ⥤ S') (hG : G ⋙ p' = p)
    (hfib : ∀ U : C, (Fiber.mapOfComp p p' G hG U).Faithful) : G.Faithful := by
  subst hG
  set q := G ⋙ p'
  constructor
  intro x y φ₁ φ₂ hGφ
  obtain ⟨w, χ, hw, hfac⟩ := exists_eqToHom_comp_map_eq hp (y := y) (q.map φ₁)
  -- both `φᵢ` factor through `χ` over the identity
  have key : ∀ φ : x ⟶ y, q.map φ₁ = q.map φ →
      ∃ α : x ⟶ w, α ≫ χ = φ ∧ q.map α = eqToHom hw.symm ∧ q.IsHomLift (𝟙 (q.obj x)) α := by
    intro φ hφ
    obtain ⟨α, ⟨hmap, hfac'⟩, -⟩ := hp.unique_lift χ φ _ (hfac.trans hφ)
    exact ⟨α, hfac', hmap, IsHomLift.of_fac' q (𝟙 (q.obj x)) α rfl hw (by rw [hmap]; simp)⟩
  obtain ⟨α₁, hα₁fac, hα₁map, h₁⟩ := key φ₁ rfl
  obtain ⟨α₂, hα₂fac, hα₂map, h₂⟩ := key φ₂ (congrArg p'.map hGφ)
  have hGα : G.map α₁ = G.map α₂ := by
    have := hp'.isStronglyCartesian (G.map χ)
    have : p'.IsHomLift (p'.map (G.map α₁)) (G.map α₂) := by
      rw [show p'.map (G.map α₁) = p'.map (G.map α₂) from hα₁map.trans hα₂map.symm]
      infer_instance
    exact IsStronglyCartesian.ext p' (p'.map (G.map χ)) (G.map χ) (p'.map (G.map α₁))
      (by rw [← G.map_comp, ← G.map_comp, hα₁fac, hα₂fac, hGφ])
  rw [← hα₁fac, ← hα₂fac,
    map_injective_of_fiber_faithful q p' G rfl (q.obj x) (hfib (q.obj x)) α₁ α₂ hGα]

/-- If `G` is full then each induced fibre functor is full: the `G`-preimage of a
morphism of the fibre of `p'` lies over the identity of `U`, because its image under `p` is its
image under `p'` after `G`. -/
private theorem full_forall_fiber_of_full (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (hG : G ⋙ p' = p) [G.Full] (U : C) : (Fiber.mapOfComp p p' G hG U).Full := by
  constructor
  intro a b t
  obtain ⟨s, hs⟩ := G.map_surjective (Fiber.fiberInclusion.map t)
  have : p.IsHomLift (𝟙 U) s := by
    refine IsHomLift.of_fac' p (𝟙 U) s a.2 b.2 ?_
    rw [map_eq_of_comp_eq p p' G hG s, hs,
      IsHomLift.fac' p' (𝟙 U) (Fiber.fiberInclusion.map t)]
    simp
  exact ⟨Fiber.homMk p U s, Fiber.hom_ext hs⟩

/-- If each induced fibre functor is full then `G` is full. -/
private theorem full_of_forall_fiber (p : S ⥤ C) (p' : S' ⥤ C) (hp : p.IsFiberedInGroupoids)
    (hp' : p'.IsFiberedInGroupoids) (G : S ⥤ S') (hG : G ⋙ p' = p)
    (hfull : ∀ U : C, (Fiber.mapOfComp p p' G hG U).Full) : G.Full := by
  subst hG
  set q := G ⋙ p'
  constructor
  intro x y s'
  obtain ⟨w, χ, hwobj, hfac⟩ := exists_eqToHom_comp_map_eq hp (y := y) (p'.map s')
  obtain ⟨t, ⟨htmap, htfac⟩, _⟩ := hp'.unique_lift (G.map χ) s' (eqToHom hwobj.symm) hfac
  have htlift : p'.IsHomLift (𝟙 (q.obj x)) t :=
    IsHomLift.of_fac' p' (𝟙 (q.obj x)) t rfl hwobj (by rw [htmap]; simp)
  set ax : q.Fiber (q.obj x) := Fiber.mk rfl
  set aw : q.Fiber (q.obj x) := Fiber.mk hwobj
  set tt : (Fiber.mapOfComp q p' G rfl (q.obj x)).obj ax
      ⟶ (Fiber.mapOfComp q p' G rfl (q.obj x)).obj aw :=
    Fiber.homMk p' (q.obj x) t with htt
  obtain ⟨aa, haa⟩ := (hfull (q.obj x)).map_surjective tt
  set s : x ⟶ w := Fiber.fiberInclusion.map aa with hs
  have hGs : G.map s = t := by
    rw [hs, ← Fiber.fiberInclusion_map_mapOfComp_map q p' G rfl (q.obj x) aa, haa, htt]
    exact Fiber.fiberInclusion_homMk p' (q.obj x) t
  exact ⟨s ≫ χ, by rw [G.map_comp, hGs, htfac]⟩

/-- **Stacks 003Z (1).** `G` is faithful if and only if for every object `U` of `C` the
induced functor `G_U : S_U ⥤ S'_U` on fibres is faithful. -/
@[stacks 003Z "(1)", sga "1 VI 6.10" "fibred in groupoids"]
theorem IsFiberedInGroupoids.faithful_iff_forall_fiber (p : S ⥤ C) (p' : S' ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hp' : p'.IsFiberedInGroupoids) (G : S ⥤ S')
    (hG : G ⋙ p' = p) : G.Faithful ↔ ∀ U : C, (Fiber.mapOfComp p p' G hG U).Faithful :=
  ⟨fun _ U => faithful_forall_fiber_of_faithful p p' G hG U,
    faithful_of_forall_fiber p p' hp hp' G hG⟩

/-- **Stacks 003Z (1).** `G` is full and faithful if and only if for every object `U` of `C` the
induced functor `G_U : S_U ⥤ S'_U` on fibres is full and faithful. -/
@[stacks 003Z "(1)", sga "1 VI 6.10" "fibred in groupoids"]
theorem IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber (p : S ⥤ C) (p' : S' ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hp' : p'.IsFiberedInGroupoids) (G : S ⥤ S')
    (hG : G ⋙ p' = p) : (G.Full ∧ G.Faithful) ↔
      ∀ U : C, ((Fiber.mapOfComp p p' G hG U).Full ∧ (Fiber.mapOfComp p p' G hG U).Faithful) :=
  ⟨fun ⟨_, _⟩ U => ⟨full_forall_fiber_of_full p p' G hG U,
      faithful_forall_fiber_of_faithful p p' G hG U⟩,
    fun h => ⟨full_of_forall_fiber p p' hp hp' G hG fun U => (h U).1,
      faithful_of_forall_fiber p p' hp hp' G hG fun U => (h U).2⟩⟩

/-- **Iso-transport into a fibre.** In a category fibred in groupoids `p`, any object `z`
together with an isomorphism `c : p.obj z ≅ U` in `C` can be transported into the fibre over
`U`: there is an object `y` over `U` and an isomorphism `β : z ≅ y` in `S` lying over
`c.hom`. -/
theorem IsFiberedInGroupoids.exists_iso_lift {p : S ⥤ C} (hp : p.IsFiberedInGroupoids) {z : S}
    {U : C} (c : p.obj z ≅ U) :
    ∃ (y : S) (_ : p.obj y = U) (β : z ≅ y), p.IsHomLift c.hom β.hom := by
  obtain ⟨y, β₀, hβ₀⟩ := hp.exists_lift c.inv z rfl
  -- a lift of an isomorphism is an isomorphism, since it is strongly cartesian
  have := hp.isStronglyCartesian_homLift c.inv β₀
  have : IsIso β₀ := IsStronglyCartesian.isIso_of_base_isIso p c.inv β₀
  have : p.IsHomLift c.symm.hom (asIso β₀).hom := hβ₀
  exact ⟨y, IsHomLift.domain_eq p c.inv β₀, (asIso β₀).symm,
    by simpa using IsHomLift.inv_lift_inv p c.symm (asIso β₀)⟩

/-- If `G` is essentially surjective then so is each induced fibre functor. -/
private theorem essSurj_forall_fiber_of_essSurj (p : S ⥤ C) (p' : S' ⥤ C)
    (hp : p.IsFiberedInGroupoids) (G : S ⥤ S') (hG : G ⋙ p' = p) [G.EssSurj] (U : C) :
    (Fiber.mapOfComp p p' G hG U).EssSurj := by
  refine ⟨fun x' => ?_⟩
  set z : S := G.objPreimage x'.val
  set β : G.obj z ≅ x'.val := G.objObjPreimageIso x'.val
  have hpgz : p'.obj (G.obj z) = p.obj z := congr_obj hG z
  have hx' : p'.obj x'.val = U := x'.property
  set c : p.obj z ≅ U := eqToIso hpgz.symm ≪≫ p'.mapIso β ≪≫ eqToIso hx' with hc
  obtain ⟨y, hy, βzy, hlift⟩ := hp.exists_iso_lift c
  set iso : G.obj y ≅ x'.val := (G.mapIso βzy).symm ≪≫ β with hiso
  -- both `β.hom` and `G.map βzy.hom` lie over `c.hom`, so `iso.hom` lies over `c.inv ≫ c.hom`
  have hβlift : p'.IsHomLift c.hom β.hom :=
    IsHomLift.of_fac' p' c.hom β.hom hpgz hx' (by rw [hc]; simp)
  have : p'.IsHomLift c.hom (G.mapIso βzy).hom :=
    (isHomLift_map_iff_of_comp_eq p p' G hG c.hom βzy.hom).2 hlift
  have : p'.IsHomLift c.inv (G.mapIso βzy).inv := IsHomLift.inv_lift_inv p' c (G.mapIso βzy)
  have : p'.IsHomLift (𝟙 U) iso.hom := by
    rw [show iso.hom = (G.mapIso βzy).inv ≫ β.hom from by rw [hiso]; simp, ← c.inv_hom_id]
    exact IsHomLift.comp p' c.inv c.hom (G.mapIso βzy).inv β.hom
  exact ⟨Fiber.mk hy, ⟨fiberIsoOfIsoOverId p' U iso⟩⟩

/-- If each induced fibre functor is essentially surjective then so is `G`: an object `x'`
of `S'` is an object of the fibre over `U := p'.obj x'`, and a fibre isomorphism onto it is
carried by the fibre inclusion to an isomorphism in `S'` exhibiting `x'` in the essential
image of `G`. -/
private theorem essSurj_of_forall_fiber (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (hG : G ⋙ p' = p) (hess : ∀ U : C, (Fiber.mapOfComp p p' G hG U).EssSurj) : G.EssSurj := by
  refine ⟨fun x' => ?_⟩
  have := hess (p'.obj x')
  set xf : p'.Fiber (p'.obj x') := Fiber.mk (p := p') (a := x') rfl
  set F := Fiber.mapOfComp p p' G hG (p'.obj x')
  exact ⟨Fiber.fiberInclusion.obj (F.objPreimage xf),
    ⟨Fiber.fiberInclusion.mapIso (F.objObjPreimageIso xf)⟩⟩

/-- **Stacks 003Z (1).** `G` is an equivalence of categories if and only if for every object
`U` of `C` the induced functor `G_U : S_U ⥤ S'_U` on fibres is an equivalence. -/
@[stacks 003Z "(1)", sga "1 VI 6.10" "fibred in groupoids", sga "1 VI 4.2" "(iii)"]
theorem IsFiberedInGroupoids.isEquivalence_iff_forall_fiber (p : S ⥤ C) (p' : S' ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hp' : p'.IsFiberedInGroupoids) (G : S ⥤ S')
    (hG : G ⋙ p' = p) :
    G.IsEquivalence ↔ ∀ U : C, (Fiber.mapOfComp p p' G hG U).IsEquivalence := by
  constructor
  · intro hGeq U
    have := hGeq.essSurj
    obtain ⟨hfull, hfaith⟩ :=
      (IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber p p' hp hp' G hG).mp
        ⟨hGeq.full, hGeq.faithful⟩ U
    have := essSurj_forall_fiber_of_essSurj p p' hp G hG U
    exact Functor.IsEquivalence.mk
  · intro hfib
    obtain ⟨hfull, hfaith⟩ :=
      (IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber p p' hp hp' G hG).mpr
        fun U => ⟨(hfib U).full, (hfib U).faithful⟩
    have := essSurj_of_forall_fiber p p' G hG fun U => (hfib U).essSurj
    exact Functor.IsEquivalence.mk

/-- **Fibrewise quasi-inverse choice data.** If `G` is an equivalence, then for every object
`x'` of `S'` there is an object `o` of `S` over the same base `p'.obj x'` together with an
isomorphism `α : x' ≅ G.obj o` in `S'` lying over the identity of `p'.obj x'`. -/
theorem quasiInverse_choice (p : S ⥤ C) (p' : S' ⥤ C) (hp : p.IsFiberedInGroupoids)
    (hp' : p'.IsFiberedInGroupoids) (G : S ⥤ S') (hG : G ⋙ p' = p) (hGequiv : G.IsEquivalence)
    (x' : S') :
    ∃ (o : S) (_ : p.obj o = p'.obj x') (α : x' ≅ G.obj o),
      p'.IsHomLift (𝟙 (p'.obj x')) α.hom := by
  have : (Fiber.mapOfComp p p' G hG (p'.obj x')).IsEquivalence :=
    (IsFiberedInGroupoids.isEquivalence_iff_forall_fiber p p' hp hp' G hG).mp hGequiv _
  set xf : p'.Fiber (p'.obj x') := Fiber.mk (p := p') (a := x') rfl
  set F := Fiber.mapOfComp p p' G hG (p'.obj x')
  -- the inverse of the chosen isomorphism in the fibre, read in `S'` along the fibre inclusion
  exact ⟨Fiber.fiberInclusion.obj (F.objPreimage xf), (F.objPreimage xf).property,
    Fiber.fiberInclusion.mapIso (F.objObjPreimageIso xf).symm, by
      rw [Functor.mapIso_hom]; infer_instance⟩

section QuasiInverse

variable (G : S ⥤ S') [G.Full] [G.Faithful] (F₀ : S' → S) (α : ∀ x' : S', x' ≅ G.obj (F₀ x'))

/-- The quasi-inverse of a fully faithful functor `G` determined by a choice, for every object
`x'` of the target, of an object `F₀ x'` of the source and an isomorphism `α x' : x' ≅ G (F₀ x')`.
On morphisms it is the `G`-preimage of the conjugate `(α x').inv ≫ g ≫ (α y').hom`. -/
noncomputable def quasiInverseOfChoice : S' ⥤ S where
  obj := F₀
  map {x' y'} g := (FullyFaithful.ofFullyFaithful G).preimage ((α x').inv ≫ g ≫ (α y').hom)
  map_id x' := G.map_injective (by simp)
  map_comp g h := G.map_injective (by simp)

/-- `G` carries a morphism of `quasiInverseOfChoice` to the conjugate of the original morphism by
the chosen isomorphisms. -/
@[simp]
theorem map_quasiInverseOfChoice_map {x' y' : S'} (g : x' ⟶ y') :
    G.map ((quasiInverseOfChoice G F₀ α).map g) = (α x').inv ≫ g ≫ (α y').hom :=
  (FullyFaithful.ofFullyFaithful G).map_preimage _

/-- The counit isomorphism `quasiInverseOfChoice ⋙ G ≅ 𝟭 S'`, the chosen isomorphisms read
backwards. -/
noncomputable def quasiInverseOfChoiceCounitIso : quasiInverseOfChoice G F₀ α ⋙ G ≅ 𝟭 S' :=
  NatIso.ofComponents (fun x' => (α x').symm) (by simp)

/-- The unit isomorphism `G ⋙ quasiInverseOfChoice ≅ 𝟭 S`, the `G`-preimage of the chosen
isomorphism at `G x`. -/
noncomputable def quasiInverseOfChoiceUnitIso : G ⋙ quasiInverseOfChoice G F₀ α ≅ 𝟭 S :=
  NatIso.ofComponents
    (fun x => ((FullyFaithful.ofFullyFaithful G).preimageIso (α (G.obj x))).symm)
    fun _ => G.map_injective (by simp [FullyFaithful.preimageIso])

/-- The component of the counit of `quasiInverseOfChoice` at `x'` is `(α x').inv`. -/
@[simp]
theorem quasiInverseOfChoiceCounitIso_hom_app (x' : S') :
    (quasiInverseOfChoiceCounitIso G F₀ α).hom.app x' = (α x').inv :=
  rfl

/-- `G` carries the component of the unit of `quasiInverseOfChoice` at `x` to
`(α (G.obj x)).inv`. -/
@[simp]
theorem map_quasiInverseOfChoiceUnitIso_hom_app (x : S) :
    G.map ((quasiInverseOfChoiceUnitIso G F₀ α).hom.app x) = (α (G.obj x)).inv :=
  (FullyFaithful.ofFullyFaithful G).map_preimage _

end QuasiInverse

/-- **Stacks 003Z (2).** If `G` is an equivalence of categories, then `G` is an equivalence
in the 2-category of categories fibred in groupoids over `C`: there are a functor
`F : S' ⥤ S` over `C` (that is, `F ⋙ p = p'`) and natural isomorphisms `G ⋙ F ≅ 𝟭 S` and
`F ⋙ G ≅ 𝟭 S'` all of whose components lie over identity morphisms of `C`. -/
@[stacks 003Z "(2)"]
theorem IsFiberedInGroupoids.isEquivalence_over (p : S ⥤ C) (p' : S' ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hp' : p'.IsFiberedInGroupoids)
    (G : S ⥤ S') (hG : G ⋙ p' = p) (hGequiv : G.IsEquivalence) :
    ∃ (F : S' ⥤ S) (_ : F ⋙ p = p') (η : G ⋙ F ≅ 𝟭 S) (ε : F ⋙ G ≅ 𝟭 S'),
      (∀ x : S, p.IsHomLift (𝟙 (p.obj x)) (η.hom.app x)) ∧
      (∀ x' : S', p'.IsHomLift (𝟙 (p'.obj x')) (ε.hom.app x')) := by
  have := hGequiv.full
  have := hGequiv.faithful
  -- for each `x'`, an object `F₀ x'` over `p'.obj x'` and an iso `α x'` lying over the identity
  choose F₀ hF₀ho α hαlift using quasiInverse_choice p p' hp hp' G hG hGequiv
  have hαho : ∀ x' : S', p'.obj x' = p'.obj (G.obj (F₀ x')) := fun x' => by
    rw [← hF₀ho, ← hG]; rfl
  have hαhom : ∀ x' : S', p'.map (α x').hom = eqToHom (hαho x') := fun x' => by
    have := hαlift x'
    simpa using IsHomLift.fac' p' (𝟙 (p'.obj x')) (α x').hom
  have hαinv : ∀ x' : S', p'.map (α x').inv = eqToHom (hαho x').symm := fun x' => by
    have := hαlift x'
    simpa using IsHomLift.fac' p' (𝟙 (p'.obj x')) (α x').inv
  refine ⟨quasiInverseOfChoice G F₀ α, ?_, quasiInverseOfChoiceUnitIso G F₀ α,
    quasiInverseOfChoiceCounitIso G F₀ α, fun x => ?_, fun x' => ?_⟩
  · refine CategoryTheory.Functor.ext hF₀ho fun x' y' g => ?_
    simp only [Functor.comp_map]
    rw [map_eq_of_comp_eq p p' G hG ((quasiInverseOfChoice G F₀ α).map g),
      map_quasiInverseOfChoice_map, p'.map_comp, p'.map_comp, hαinv, hαhom]
    simp
  · have := hαlift (G.obj x)
    have hpgx : p'.obj (G.obj x) = p.obj x := congr_obj hG x
    refine (isHomLift_map_iff_of_comp_eq p p' G hG (𝟙 (p.obj x)) _).1 ?_
    rw [map_quasiInverseOfChoiceUnitIso_hom_app, ← hpgx]
    infer_instance
  · have := hαlift x'
    rw [quasiInverseOfChoiceCounitIso_hom_app]
    infer_instance

end CategoryTheory.Functor

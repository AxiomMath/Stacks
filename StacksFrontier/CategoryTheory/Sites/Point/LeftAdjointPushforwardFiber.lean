module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre of the left adjoint of a direct image, at a point

Let `G : D ⥤ C` be a continuous functor between sites `(D, K)` and `(C, J)`, so that
precomposition with `G` is a functor `G_* : Sh(C, A) ⥤ Sh(D, A)`, and let `G^! ⊣ G_*` be a left
adjoint of it — for instance the extension by zero `j_!` along an object of a site, where `G` is
the forgetful functor of a slice. Let `Φ` be a point of `(C, J)` and let `(Ψ i)_{i ∈ I}` be a
family of points of `(D, K)` such that the fibre of `Φ` along `G` decomposes as the disjoint
union of the fibres of the `Ψ i`:
```
  Φ(G W) = ∐_{i ∈ I} Ψ_i(W)     naturally in `W : D`.
```
Then the fibre at `Φ` of `G^! F` is the coproduct of the fibres of `F` at the `Ψ i`:
```
  (G^! F)_Φ = ∐_{i ∈ I} F_{Ψ_i}     naturally in `F`.
```
This is Stacks 04H4 and Stacks 03S5 (the stalk formula for `j_!`) in the generality of a left
adjoint of a direct image, for sheaves with values in any category with the products and
colimits the fibre functors and the skyscraper sheaves need; the coefficients are not required to
be sets or abelian groups, and the universe of the fibres is free.

The proof identifies both sides as left adjoints of the same functor. The fibre at `Φ` of `G^!`
is the composite of two left adjoints, so it is left adjoint to `G_*` applied to the skyscraper
sheaf at `Φ`. That restricted skyscraper sheaf has, over `W`, the product of copies of `M`
indexed by `Φ(G W)`; so a morphism into it from `F` is a compatible family of morphisms
`F(W) ⟶ M` indexed by the elements of `Ψ_i(W)` for all `i`, which is a family of morphisms out
of the fibres `F_{Ψ_i}`, which is a morphism out of their coproduct.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.sigmaSheafFiber`: the coproduct of the fibres of a
  sheaf at a family of points, as a functor of the sheaf.
* `CategoryTheory.GrothendieckTopology.Point.sigmaSheafFiberAdjunction`: it is left adjoint to
  the direct image along `G` of the skyscraper sheaf at `Φ`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.sheafFiberLeftAdjointIso`: the fibre at `Φ` of a
  left adjoint of the direct image along `G` is the coproduct of the fibres at the `Ψ i`.

## References

* [Stacks Project, Tag 04H4](https://stacks.math.columbia.edu/tag/04H4)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ v' u₁ u₂ u'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
  (G : D ⥤ C) [G.IsContinuous K J]
  (Φ : Point.{w} J) {ι : Type w} (Ψ : ι → Point.{w} K)
  (e : ∀ W : D, (Σ i, (Ψ i).fiber.obj W) ≃ Φ.fiber.obj (G.obj W))
  (he : ∀ ⦃W V : D⦄ (f : W ⟶ V) (i : ι) (w : (Ψ i).fiber.obj W),
    Φ.fiber.map (G.map f) (e W ⟨i, w⟩) = e V ⟨i, (Ψ i).fiber.map f w⟩)

/-- The coproduct of the fibres of a sheaf at the points `Ψ i`, as a functor of the sheaf. -/
abbrev sigmaSheafFiber : Sheaf K A ⥤ A :=
  Functor.pi' (fun i => (Ψ i).sheafFiber (A := A)) ⋙ Sigma.functor ι

variable (K) in
/-- The direct image along `G` of the skyscraper sheaf at `Φ`. Over `W` its sections are the
product of copies of the value indexed by the fibre `Φ(G W)`. -/
@[ega "IV 21.9.1" "more general"]
abbrev pushforwardSkyscraper : A ⥤ Sheaf K A :=
  Φ.skyscraperSheafFunctor ⋙ G.sheafPushforwardContinuous A K J

variable (K) in
/-- The projection of the sections over `W` of the direct image of the skyscraper sheaf to the
copy indexed by an element `q` of `Φ(G W)`. -/
def pushforwardSkyscraperπ (M : A) (W : D) (q : Φ.fiber.obj (G.obj W)) :
    ((pushforwardSkyscraper K G Φ).obj M).obj.obj (op W) ⟶ M :=
  Pi.π (fun _ => M) q

variable {G Φ} in
omit [HasColimitsOfSize.{w, w, v', u'} A] in
/-- Two maps into the sections of the direct image of the skyscraper sheaf agree as soon as all
their components agree. -/
lemma pushforwardSkyscraper_hom_ext {M : A} {W : D} {Y : A}
    {a b : Y ⟶ ((pushforwardSkyscraper K G Φ).obj M).obj.obj (op W)}
    (h : ∀ q, a ≫ pushforwardSkyscraperπ K G Φ M W q = b ≫ pushforwardSkyscraperπ K G Φ M W q) :
    a = b :=
  Pi.hom_ext _ _ h

omit [HasColimitsOfSize.{w, w, v', u'} A] in
/-- The restriction maps of the direct image of the skyscraper sheaf reindex the product along
the action of the fibre functor. -/
lemma pushforwardSkyscraper_obj_map_π (M : A) {W V : D} (f : W ⟶ V)
    (q : Φ.fiber.obj (G.obj W)) :
    ((pushforwardSkyscraper K G Φ).obj M).obj.map f.op ≫ pushforwardSkyscraperπ K G Φ M W q =
      pushforwardSkyscraperπ K G Φ M V (Φ.fiber.map (G.map f) q) :=
  (Limits.Pi.map'_comp_π
    (f := fun _ : Φ.fiber.obj (G.obj V) => M) (g := fun _ : Φ.fiber.obj (G.obj W) => M)
    (Φ.fiber.map (G.map f)) (fun _ => 𝟙 M) q).trans (Category.comp_id _)

omit [HasColimitsOfSize.{w, w, v', u'} A] in
/-- Postcomposition with a map acts componentwise on the direct image of the skyscraper
sheaf. -/
lemma pushforwardSkyscraperπ_naturality {M N : A} (g : M ⟶ N) (W : D)
    (q : Φ.fiber.obj (G.obj W)) :
    ((pushforwardSkyscraper K G Φ).map g).hom.app (op W) ≫ pushforwardSkyscraperπ K G Φ N W q =
      pushforwardSkyscraperπ K G Φ M W q ≫ g :=
  Pi.map_π (fun _ => g) q

variable {G Φ Ψ}

omit [HasColimitsOfSize.{w, w, v', u'} A] in
/-- Two maps into the direct image of the skyscraper sheaf agree as soon as their components
indexed by `e W ⟨i, w⟩` agree. -/
private lemma hom_ext_pushforwardSkyscraper {F : Sheaf K A} {M : A}
    {a b : F ⟶ (pushforwardSkyscraper K G Φ).obj M}
    (h : ∀ (W : D) (i : ι) (w : (Ψ i).fiber.obj W),
      a.hom.app (op W) ≫ pushforwardSkyscraperπ K G Φ M W (e W ⟨i, w⟩) =
        b.hom.app (op W) ≫ pushforwardSkyscraperπ K G Φ M W (e W ⟨i, w⟩)) :
    a = b := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext ⟨W⟩
  refine pushforwardSkyscraper_hom_ext fun q => ?_
  obtain ⟨⟨i, w⟩, rfl⟩ := (e W).surjective q
  exact h W i w

variable (F : Sheaf K A) (M : A)

/-- The component at `W` of the map to the direct image of the skyscraper sheaf determined by a
family of maps out of the fibres at the `Ψ i`. -/
def fiberFamilyToPushforwardSkyscraperApp (f : ∀ i, (Ψ i).sheafFiber.obj F ⟶ M) (W : D) :
    F.obj.obj (op W) ⟶ ((pushforwardSkyscraper K G Φ).obj M).obj.obj (op W) :=
  Pi.lift fun q =>
    (Ψ ((e W).symm q).1).toPresheafFiber W ((e W).symm q).2 F.obj ≫ f ((e W).symm q).1

/-- The defining formula for the components of `fiberFamilyToPushforwardSkyscraperApp`. -/
lemma fiberFamilyToPushforwardSkyscraperApp_π (f : ∀ i, (Ψ i).sheafFiber.obj F ⟶ M) (W : D)
    (i : ι) (w : (Ψ i).fiber.obj W) :
    fiberFamilyToPushforwardSkyscraperApp e F M f W ≫
        pushforwardSkyscraperπ K G Φ M W (e W ⟨i, w⟩) =
      (Ψ i).toPresheafFiber W w F.obj ≫ f i := by
  change Pi.lift _ ≫ Pi.π _ (e W ⟨i, w⟩) = _
  rw [Pi.lift_π, Equiv.symm_apply_apply]

/-- A family of maps out of the fibres at the `Ψ i` assembles into a map to the direct image of
the skyscraper sheaf. -/
def fiberFamilyToPushforwardSkyscraper (f : ∀ i, (Ψ i).sheafFiber.obj F ⟶ M) :
    F ⟶ (pushforwardSkyscraper K G Φ).obj M where
  hom :=
    { app W := fiberFamilyToPushforwardSkyscraperApp e F M f W.unop
      naturality {W V} g := by
        refine pushforwardSkyscraper_hom_ext fun q => ?_
        obtain ⟨⟨i, w⟩, rfl⟩ := (e V.unop).surjective q
        rw [← Quiver.Hom.op_unop g, Category.assoc, fiberFamilyToPushforwardSkyscraperApp_π,
          Category.assoc, pushforwardSkyscraper_obj_map_π, he,
          fiberFamilyToPushforwardSkyscraperApp_π]
        exact (Ψ i).toPresheafFiber_w_assoc g.unop w F.obj (f i) }

/-- A map to the direct image of the skyscraper sheaf restricts to a map out of the fibre at each
`Ψ i`. -/
def pushforwardSkyscraperToFiberFamily (g : F ⟶ (pushforwardSkyscraper K G Φ).obj M) (i : ι) :
    (Ψ i).sheafFiber.obj F ⟶ M :=
  (Ψ i).presheafFiberDesc
    (fun W w => g.hom.app (op W) ≫ pushforwardSkyscraperπ K G Φ M W (e W ⟨i, w⟩)) (by
      intro W V f w
      change F.obj.map f.op ≫ (g.hom.app (op W) ≫
        pushforwardSkyscraperπ K G Φ M W (e W ⟨i, w⟩)) = _
      rw [← Category.assoc, g.hom.naturality f.op, Category.assoc,
        pushforwardSkyscraper_obj_map_π, he])

/-- Families of maps out of the fibres at the `Ψ i` correspond to maps into the direct image of
the skyscraper sheaf at `Φ`. -/
def fiberFamilyPushforwardSkyscraperEquiv :
    (∀ i, (Ψ i).sheafFiber.obj F ⟶ M) ≃ (F ⟶ (pushforwardSkyscraper K G Φ).obj M) where
  toFun := fiberFamilyToPushforwardSkyscraper e he F M
  invFun := pushforwardSkyscraperToFiberFamily e he F M
  left_inv f := by
    funext i
    apply (Ψ i).presheafFiber_hom_ext
    intro W w
    simp only [pushforwardSkyscraperToFiberFamily,
      GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
    exact fiberFamilyToPushforwardSkyscraperApp_π e F M f W i w
  right_inv g := by
    refine hom_ext_pushforwardSkyscraper e fun W i w => ?_
    change fiberFamilyToPushforwardSkyscraperApp e F M _ W ≫
      pushforwardSkyscraperπ K G Φ M W (e W ⟨i, w⟩) = _
    rw [fiberFamilyToPushforwardSkyscraperApp_π]
    exact (Ψ i).toPresheafFiber_presheafFiberDesc _ _ W w

/-- Maps out of the coproduct of the fibres at the `Ψ i` correspond to maps into the direct image
of the skyscraper sheaf at `Φ`. -/
def sigmaSheafFiberHomEquiv :
    ((sigmaSheafFiber Ψ).obj F ⟶ M) ≃ (F ⟶ (pushforwardSkyscraper K G Φ).obj M) :=
  (show (∐ (fun i => (Ψ i).sheafFiber.obj F) ⟶ M) ≃ (∀ i, (Ψ i).sheafFiber.obj F ⟶ M) from
    { toFun := fun f i => Sigma.ι (fun i => (Ψ i).sheafFiber.obj F) i ≫ f
      invFun := fun f => Sigma.desc f
      left_inv f := Sigma.hom_ext _ _ fun i => by simp
      right_inv f := by
        funext i
        simp }).trans
    (fiberFamilyPushforwardSkyscraperEquiv e he F M)

/-- The germ of a section of a sheaf at a point, with target the fibre of the sheaf. -/
abbrev sheafFiberGerm (Ψ' : Point.{w} K) (F : Sheaf K A) (W : D) (w : Ψ'.fiber.obj W) :
    F.obj.obj (op W) ⟶ Ψ'.sheafFiber.obj F :=
  Ψ'.toPresheafFiber W w F.obj

/-- The inclusion of the fibre at `Ψ i` into the coproduct of the fibres. -/
abbrev sigmaSheafFiberι (F : Sheaf K A) (i : ι) :
    (Ψ i).sheafFiber.obj F ⟶ (sigmaSheafFiber Ψ).obj F :=
  Sigma.ι (fun i => (Ψ i).sheafFiber.obj F) i

/-- The defining formula for the components of `sigmaSheafFiberHomEquiv`. -/
lemma sigmaSheafFiberHomEquiv_π (f : (sigmaSheafFiber Ψ).obj F ⟶ M) (W : D) (i : ι)
    (w : (Ψ i).fiber.obj W) :
    (sigmaSheafFiberHomEquiv e he F M f).hom.app (op W) ≫
        pushforwardSkyscraperπ K G Φ M W (e W ⟨i, w⟩) =
      sheafFiberGerm (Ψ i) F W w ≫ sigmaSheafFiberι F i ≫ f :=
  fiberFamilyToPushforwardSkyscraperApp_π e F M _ W i w

omit [HasProducts A] in
/-- The coproduct of the fibres is functorial summandwise. -/
lemma sigmaSheafFiberι_map_assoc {F F' : Sheaf K A} (f : F ⟶ F') (i : ι) {T : A}
    (h : (sigmaSheafFiber Ψ).obj F' ⟶ T) :
    sigmaSheafFiberι F i ≫ (sigmaSheafFiber Ψ).map f ≫ h =
      (Ψ i).sheafFiber.map f ≫ sigmaSheafFiberι F' i ≫ h :=
  Sigma.ι_map_assoc _ i h

omit [HasProducts A] in
/-- The germ into a summand of the coproduct of the fibres is natural in the sheaf. -/
lemma sheafFiberGerm_ι_map_assoc {F F' : Sheaf K A} (f : F ⟶ F') (i : ι)
    (W : D) (w : (Ψ i).fiber.obj W) {T : A} (h : (sigmaSheafFiber Ψ).obj F' ⟶ T) :
    sheafFiberGerm (Ψ i) F W w ≫ sigmaSheafFiberι F i ≫ (sigmaSheafFiber Ψ).map f ≫ h =
      f.hom.app (op W) ≫ sheafFiberGerm (Ψ i) F' W w ≫ sigmaSheafFiberι F' i ≫ h := by
  rw [sigmaSheafFiberι_map_assoc]
  exact (Ψ i).toPresheafFiber_naturality_assoc f.hom W w _

variable (G Φ Ψ)

/-- The coproduct of the fibres at the points `Ψ i` is left adjoint to the direct image along
`G` of the skyscraper sheaf at `Φ`. -/
def sigmaSheafFiberAdjunction : sigmaSheafFiber Ψ ⊣ pushforwardSkyscraper (A := A) K G Φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sigmaSheafFiberHomEquiv e he
      homEquiv_naturality_left_symm := by
        intro F F' M f g
        apply (sigmaSheafFiberHomEquiv e he F M).injective
        refine hom_ext_pushforwardSkyscraper e fun W i w => ?_
        rw [Equiv.apply_symm_apply]
        change (f.hom.app (op W) ≫ g.hom.app (op W)) ≫
          pushforwardSkyscraperπ K G Φ M W (e W ⟨i, w⟩) = _
        rw [sigmaSheafFiberHomEquiv_π]
        change _ = sheafFiberGerm (Ψ i) F W w ≫ sigmaSheafFiberι F i ≫
          (sigmaSheafFiber Ψ).map f ≫ (sigmaSheafFiberHomEquiv e he F' M).symm g
        rw [sheafFiberGerm_ι_map_assoc]
        have h := sigmaSheafFiberHomEquiv_π e he F' M
          ((sigmaSheafFiberHomEquiv e he F' M).symm g) W i w
        rw [Equiv.apply_symm_apply] at h
        rw [Category.assoc, h]
      homEquiv_naturality_right := by
        intro F M N f g
        refine hom_ext_pushforwardSkyscraper e fun W i w => ?_
        rw [sigmaSheafFiberHomEquiv_π, ObjectProperty.FullSubcategory.comp_hom,
          NatTrans.comp_app, Category.assoc, pushforwardSkyscraperπ_naturality,
          ← Category.assoc ((sigmaSheafFiberHomEquiv e he F M f).hom.app (op W)),
          sigmaSheafFiberHomEquiv_π]
        simp only [Category.assoc] }

/-- **The fibre of a left adjoint of a direct image (Stacks 04H4, 03S5).** Let `G^!` be a left
adjoint of the direct image `G_*` along a continuous functor `G : D ⥤ C`, let `Φ` be a point of
`C` and let `(Ψ i)` be points of `D` whose fibres decompose the fibre of `Φ` along `G`,
`Φ(G W) = ∐_i Ψ_i(W)` naturally in `W`. Then the fibre at `Φ` of `G^! F` is the coproduct of
the fibres of `F` at the `Ψ i`, naturally in `F`. -/
def sheafFiberLeftAdjointIso (L : Sheaf K A ⥤ Sheaf J A)
    (adj : L ⊣ G.sheafPushforwardContinuous A K J) :
    L ⋙ Φ.sheafFiber ≅ sigmaSheafFiber (A := A) Ψ :=
  (adj.comp Φ.skyscraperSheafAdjunction).leftAdjointUniq (sigmaSheafFiberAdjunction G Φ Ψ e he)

end CategoryTheory.GrothendieckTopology.Point

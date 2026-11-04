module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationEndomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections

/-!
# The Frobenius on the stalk of `j_* F` at a boundary point

An endomorphism `a` of a geometric point `s : Spec Ω ⟶ S` over `S` (for a geometric point over a
closed point with finite residue field, a lift of the Frobenius) is a morphism of points of
Mathlib's small étale site of `S` (SGA 4 IV 3.2): on the fibre functor `V ↦ Hom_S(Spec Ω, V)` it
acts by precomposition with `a`. It therefore acts on every stalk at `s`, naturally in the sheaf,
sending the germ at `(V, v)` to the germ at `(V, v ∘ a)`: this is the map of Tag 04FN on Mathlib's
site, and on the stalk of `j_* F` at a boundary point it is the Frobenius on `H⁰_loc` of
Weil II 1.8.

## Main definitions

* `AlgebraicGeometry.pointSmallEtaleHom` — the morphism of points of the small étale site given
  by a morphism of geometric points; for `s = s'` the endomorphism given by `a`.

## Main results

* `AlgebraicGeometry.toPresheafFiber_pointSmallEtaleHom` — its action on germs.

## References

* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme

universe w w' u v u' v'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  [HasColimitsOfSize.{w, w} A] [HasProducts.{w} A] [HasWeakSheafify J A]

/-- **The identification of the fibre of a sheafification with the fibre of the presheaf is
natural in the point**: it is the inverse of the fibre of the unit of sheafification, and the map
of fibres induced by a morphism of points is natural in the presheaf. -/
theorem Hom.presheafToSheafCompSheafFiberIso_hom_naturality {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂)
    (P : Cᵒᵖ ⥤ A) :
    (Φ₂.presheafToSheafCompSheafFiberIso A).hom.app P ≫ f.presheafFiber.app P =
      f.sheafFiber.app ((presheafToSheaf J A).obj P) ≫
        (Φ₁.presheafToSheafCompSheafFiberIso A).hom.app P := by
  have key : (Φ₂.presheafToSheafCompSheafFiberIso A).inv.app P ≫
      f.sheafFiber.app ((presheafToSheaf J A).obj P) =
      f.presheafFiber.app P ≫ (Φ₁.presheafToSheafCompSheafFiberIso A).inv.app P :=
    f.presheafFiber.naturality (CategoryTheory.toSheafify J P)
  rw [← cancel_epi ((Φ₂.presheafToSheafCompSheafFiberIso A).inv.app P),
    Iso.inv_hom_id_app_assoc, reassoc_of% key, Iso.inv_hom_id_app, Category.comp_id]

/-- **The germ formula for the fibre of a left Kan extension** (the inverse of
`presheafFiberLanIso`): the germ at `(X, x)` of a section `p` of `P` goes to the germ at
`(G X, e x)` of the image of `p` in the left Kan extension. -/
theorem toPresheafFiber_presheafFiberLanIso_inv_app
    {C' : Type u} [Category.{v} C'] {D : Type u'} [Category.{v'} D]
    {J' : GrothendieckTopology C'} {K : GrothendieckTopology D}
    (Φ : GrothendieckTopology.Point.{w} J') (Ψ : GrothendieckTopology.Point.{w} K) (G : C' ⥤ D)
    [∀ (F : C'ᵒᵖ ⥤ Type (max w w')), G.op.HasLeftKanExtension F]
    (e : Φ.fiber ≅ G ⋙ Ψ.fiber) (P : C'ᵒᵖ ⥤ Type (max w w')) (X : C') (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ (presheafFiberLanIso.{w, w'} Φ Ψ G e).inv.app P =
      (G.op.lanUnit.app P).app (op X) ≫
        Ψ.toPresheafFiber (G.obj X) (e.hom.app X x) (G.op.lan.obj P) := by
  unfold presheafFiberLanIso
  simp only [Adjunction.leftAdjointUniq_inv_app]
  rw [← Equiv.symm_apply_apply (Φ.skyscraperPresheafAdjunction.homEquiv _ _)
    ((Φ.skyscraperPresheafAdjunction.leftAdjointUniq _).hom.app P),
    Adjunction.homEquiv_leftAdjointUniq_hom_app, skyscraperPresheafAdjunction_homEquiv_symm_apply,
    toPresheafFiber_skyscraperPresheafHomEquiv_symm]
  simp only [Functor.comp_obj, Adjunction.ofNatIsoRight, NatTrans.comp_app, Functor.id_obj,
    Functor.whiskeringLeft_obj_obj, Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app, Category.assoc, Functor.op_obj]
  refine (Category.assoc _ _ _).trans (congrArg ((G.op.lanUnit.app P).app (op X) ≫ ·) ?_)
  change ((Ψ.skyscraperPresheafAdjunction.unit.app (G.op.lan.obj P)).app (op (G.obj X)) ≫
      Pi.map' (ConcreteCategory.hom (e.hom.app X))
        (fun _ => 𝟙 (Ψ.presheafFiber.obj (G.op.lan.obj P)))) ≫
      Pi.π (fun _ => Ψ.presheafFiber.obj (G.op.lan.obj P)) x = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((Ψ.skyscraperPresheafAdjunction.unit.app (G.op.lan.obj P)).app
    (op (G.obj X)) ≫ ·) (Pi.map'_comp_π _ _ x)).trans ?_
  refine (congrArg ((Ψ.skyscraperPresheafAdjunction.unit.app (G.op.lan.obj P)).app
    (op (G.obj X)) ≫ ·) (Category.comp_id _)).trans ?_
  have hu := Ψ.skyscraperPresheafHomEquiv_app_π (𝟙 (Ψ.presheafFiber.obj (G.op.lan.obj P)))
    (G.obj X) (ConcreteCategory.hom (e.hom.app X) x)
  rwa [Category.comp_id] at hu

/-- A morphism of points acts on germs through its map of fibre functors. -/
theorem Hom.toPresheafFiber_presheafFiber_app {C' : Type u} [Category.{v} C']
    {J' : GrothendieckTopology C'} {A' : Type*} [Category* A'] [HasColimitsOfSize.{w, w} A']
    {Φ₁ Φ₂ : Point.{w} J'} (f : Φ₁ ⟶ Φ₂) (P : C'ᵒᵖ ⥤ A') (X : C') (x : Φ₂.fiber.obj X) :
    Φ₂.toPresheafFiber X x P ≫ f.presheafFiber.app P =
      Φ₁.toPresheafFiber X (ConcreteCategory.hom (f.hom.app X) x) P := by
  simp only [Hom.presheafFiber_app, toPresheafFiber_presheafFiberDesc]

/-- **The fibre of a left Kan extension is identified with the fibre of the presheaf naturally in
the pair of points**: for morphisms of points `f : Φ₁ ⟶ Φ₂` and `g : Ψ₁ ⟶ Ψ₂` compatible with the
identifications `e₁, e₂` of the fibre functors, `presheafFiberLanIso` intertwines them. -/
theorem presheafFiberLanIso_inv_naturality
    {C' : Type u} [Category.{v} C'] {D : Type u'} [Category.{v'} D]
    {J' : GrothendieckTopology C'} {K : GrothendieckTopology D}
    (Φ₁ Φ₂ : GrothendieckTopology.Point.{w} J') (Ψ₁ Ψ₂ : GrothendieckTopology.Point.{w} K)
    (G : C' ⥤ D) [∀ (F : C'ᵒᵖ ⥤ Type (max w w')), G.op.HasLeftKanExtension F]
    (e₁ : Φ₁.fiber ≅ G ⋙ Ψ₁.fiber) (e₂ : Φ₂.fiber ≅ G ⋙ Ψ₂.fiber) (f : Φ₁ ⟶ Φ₂) (g : Ψ₁ ⟶ Ψ₂)
    (hfg : f.hom ≫ e₁.hom = e₂.hom ≫ Functor.whiskerLeft G g.hom) (P : C'ᵒᵖ ⥤ Type (max w w')) :
    f.presheafFiber.app P ≫ (presheafFiberLanIso.{w, w'} Φ₁ Ψ₁ G e₁).inv.app P =
      (presheafFiberLanIso.{w, w'} Φ₂ Ψ₂ G e₂).inv.app P ≫
        g.presheafFiber.app (G.op.lan.obj P) := by
  ext X x : 1
  rw [reassoc_of% (Hom.toPresheafFiber_presheafFiber_app f P X x),
    toPresheafFiber_presheafFiberLanIso_inv_app,
    reassoc_of% (toPresheafFiber_presheafFiberLanIso_inv_app Φ₂ Ψ₂ G e₂ P X x),
    Hom.toPresheafFiber_presheafFiber_app]
  congr 2
  exact ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ X) hfg) x

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **A morphism of geometric points is a morphism of points of the small étale site**: for
`a : Spec Ω ⟶ Spec Ω` with `a ≫ s' = s`, precomposition with `a` maps the fibre functor
`V ↦ Hom_S(Spec Ω, V)` at `s'` to the one at `s`. -/
def pointSmallEtaleHom (s s' : Spec (.of Ω) ⟶ S) (a : Spec (.of Ω) ⟶ Spec (.of Ω))
    (ha : a ≫ s' = s) : pointSmallEtale s ⟶ pointSmallEtale s' :=
  ⟨Functor.whiskerLeft (Scheme.Etale.forget S)
    (coyoneda.map (Over.homMk a ha : Over.mk s ⟶ Over.mk s').op)⟩

/-- **The action of a morphism of geometric points on germs**: the germ at `(V, v)` goes to the
germ at `(V, v ∘ a)`. -/
theorem toPresheafFiber_pointSmallEtaleHom {A : Type v} [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] (s s' : Spec (.of Ω) ⟶ S) (a : Spec (.of Ω) ⟶ Spec (.of Ω))
    (ha : a ≫ s' = s) (P : S.Etaleᵒᵖ ⥤ A) (X : S.Etale) (x : (pointSmallEtale s').fiber.obj X) :
    (pointSmallEtale s').toPresheafFiber X x P ≫
        (pointSmallEtaleHom s s' a ha).presheafFiber.app P =
      (pointSmallEtale s).toPresheafFiber X
        ((Over.homMk a ha : Over.mk s ⟶ Over.mk s') ≫ x) P := by
  simp only [GrothendieckTopology.Point.Hom.presheafFiber_app,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
  rfl

/-- **The identification of the fibre functor at `s ≫ i` with base change followed by the fibre
functor at `s` is natural in the geometric point**: it is the adjunction `Over.map i ⊣
Over.pullback i`, natural in the source object. -/
theorem pointSmallEtaleBaseChangeFiberIso_naturality {Z X : Scheme.{u}} (i : Z ⟶ X)
    (s s' : Spec (.of Ω) ⟶ Z) (a : Spec (.of Ω) ⟶ Spec (.of Ω)) (ha : a ≫ s' = s) :
    (Stacks.EtaleCohomology.pointSmallEtaleBaseChangeFiberIso i s').hom ≫
        Functor.whiskerLeft (Stacks.EtaleCohomology.smallEtaleBaseChange i)
          (pointSmallEtaleHom s s' a ha).hom =
      (pointSmallEtaleHom (s ≫ i) (s' ≫ i) a (by rw [← Category.assoc, ha])).hom ≫
        (Stacks.EtaleCohomology.pointSmallEtaleBaseChangeFiberIso i s).hom := by
  ext U q
  exact ((Over.mapPullbackAdj i).homEquiv_naturality_left
    (Over.homMk a ha : Over.mk s ⟶ Over.mk s') q).symm

/-- **The stalk of an inverse image at `s` is the stalk at `s ≫ i`, naturally in the geometric
point** (Stacks 03Q1, compatibility with morphisms of geometric points): for `a` with
`a ≫ s' = s`, the identification `(i⁻¹ F)_s ≅ F_{s ≫ i}` intertwines the maps induced by `a`. -/
theorem smallEtaleInverseImageStalkIso_hom_naturality {Z X : Scheme.{u}} (i : Z ⟶ X)
    (s s' : Spec (.of Ω) ⟶ Z) (a : Spec (.of Ω) ⟶ Spec (.of Ω)) (ha : a ≫ s' = s)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) :
    (pointSmallEtaleHom s s' a ha).sheafFiber.app
        ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} i).obj F) ≫
      (Stacks.EtaleCohomology.smallEtaleInverseImageStalkIso.{v, u} i s).hom.app F =
    (Stacks.EtaleCohomology.smallEtaleInverseImageStalkIso.{v, u} i s').hom.app F ≫
      (pointSmallEtaleHom (s ≫ i) (s' ≫ i) a (by rw [← Category.assoc, ha])).sheafFiber.app F := by
  have hA := GrothendieckTopology.Point.Hom.presheafToSheafCompSheafFiberIso_hom_naturality
    (A := Type (max (u + 1) v)) (pointSmallEtaleHom s s' a ha)
    ((Stacks.EtaleCohomology.smallEtaleBaseChange i).op.lan.obj F.obj)
  have hB := GrothendieckTopology.Point.presheafFiberLanIso_inv_naturality.{u, max (u + 1) v}
    (pointSmallEtale (s ≫ i)) (pointSmallEtale (s' ≫ i)) (pointSmallEtale s) (pointSmallEtale s')
    (Stacks.EtaleCohomology.smallEtaleBaseChange i)
    (Stacks.EtaleCohomology.pointSmallEtaleBaseChangeFiberIso i s)
    (Stacks.EtaleCohomology.pointSmallEtaleBaseChangeFiberIso i s')
    (pointSmallEtaleHom (s ≫ i) (s' ≫ i) a (by rw [← Category.assoc, ha]))
    (pointSmallEtaleHom s s' a ha)
    (pointSmallEtaleBaseChangeFiberIso_naturality i s s' a ha).symm F.obj
  have hB' := (Iso.app (GrothendieckTopology.Point.presheafFiberLanIso.{u, max (u + 1) v}
      (pointSmallEtale (s' ≫ i)) (pointSmallEtale s')
      (Stacks.EtaleCohomology.smallEtaleBaseChange i)
      (Stacks.EtaleCohomology.pointSmallEtaleBaseChangeFiberIso i s')) F.obj).eq_inv_comp.1
    ((Iso.app (GrothendieckTopology.Point.presheafFiberLanIso.{u, max (u + 1) v}
      (pointSmallEtale (s ≫ i)) (pointSmallEtale s)
      (Stacks.EtaleCohomology.smallEtaleBaseChange i)
      (Stacks.EtaleCohomology.pointSmallEtaleBaseChangeFiberIso i s)) F.obj).comp_inv_eq.1 hB
        |>.trans (Category.assoc _ _ _))
  simp only [Stacks.EtaleCohomology.smallEtaleInverseImageStalkIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.associator_inv_app, Category.id_comp]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hA.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hB'.symm).trans ?_
  exact (Category.assoc _ _ _).symm

section ClosedPoint

open Stacks.EtaleCohomology

variable {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω]
  [IsAlgClosed Ω]

omit [StrictlyHenselianLocalRing R] in
/-- **Over a strictly henselian local ring the germ of a global section at a geometric point
above the closed point is compatible with morphisms of geometric points**: both are germs at the
final object of the small étale site, whose lift of each geometric point is unique. -/
theorem sectionsToPresheafFiberClosedPoint_pointSmallEtaleHom (y y' : Spec (.of Ω) ⟶ Spec (.of R))
    (a : Spec (.of Ω) ⟶ Spec (.of Ω)) (ha : a ≫ y' = y) :
    sectionsToPresheafFiberClosedPoint.{u, v} y' ≫
        (pointSmallEtaleHom y y' a ha).presheafFiber =
      sectionsToPresheafFiberClosedPoint.{u, v} y := by
  ext P : 2
  refine (toPresheafFiber_pointSmallEtaleHom y y' a ha P _ _).trans ?_
  congr 1
  exact Over.OverMorphism.ext ha

/-- **The identification of global sections with the stalk at a closed geometric point is
compatible with morphisms of geometric points**, at the level of sheaves. -/
theorem sheafFiberClosedPointIsoGamma_inv_pointSmallEtaleHom (y y' : Spec (.of Ω) ⟶ Spec (.of R))
    (hy : y (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)
    (hy' : y' (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω)) (ha : a ≫ y' = y) :
    (sheafFiberClosedPointIsoGamma.{u, v} y' hy').inv ≫
        (pointSmallEtaleHom y y' a ha).sheafFiber =
      (sheafFiberClosedPointIsoGamma.{u, v} y hy).inv := by
  refine NatTrans.ext (funext fun G => ?_)
  have h := congrArg (fun φ => NatTrans.app φ G.obj)
    (sectionsToPresheafFiberClosedPoint_pointSmallEtaleHom.{u, v} y y' a ha)
  simp only [NatTrans.comp_app] at h
  simp only [sheafFiberClosedPointIsoGamma, presheafFiberClosedPointIsoSections,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  exact congrArg (_ ≫ ·) h

variable {S : Scheme.{u}} (π : Spec (.of R) ⟶ S)

/-- **The stalk of a sheaf at the image of a closed geometric point of a strictly henselian local
scheme `Spec R ⟶ S` is the set of sections of its inverse image over `Spec R`**: the stalk of the
inverse image (Stacks 03Q1) followed by the sections over the final object. -/
def closedPointStalkIsoGamma (y : Spec (.of Ω) ⟶ Spec (.of R))
    (hy : y (default : Spec (.of Ω)) = IsLocalRing.closedPoint R) :
    (pointSmallEtale (y ≫ π)).sheafFiber (A := Type (max (u + 1) v)) ≅
      Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} π ⋙
        Sheaf.Γ (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v)) :=
  (Stacks.EtaleCohomology.smallEtaleInverseImageStalkIso.{v, u} π y).symm ≪≫
    Functor.isoWhiskerLeft (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} π)
      (sheafFiberClosedPointIsoGamma.{u, v} y hy)

/-- **Changing the closed geometric point along `a` is the map of stalks induced by `a`**: for
closed geometric points `y, y'` of `Spec R` with `a ≫ y' = y`, the identifications of the stalks
at `y ≫ π` and `y' ≫ π` with the sections of the inverse image differ by the morphism of points
given by `a`. For an endomorphism `a` of a geometric point of `S` (a Frobenius) and `y'` the
canonical lift to the strict henselization, `y = a ≫ y'`: the Frobenius on the stalk is
`Θ_{y'}⁻¹ ∘ Θ_{a ≫ y'}`. -/
theorem pointSmallEtaleHom_sheafFiber_closedPointStalkIsoGamma_hom
    (y y' : Spec (.of Ω) ⟶ Spec (.of R))
    (hy : y (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)
    (hy' : y' (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω)) (ha : a ≫ y' = y) :
    (pointSmallEtaleHom (y ≫ π) (y' ≫ π) a (by rw [← Category.assoc, ha])).sheafFiber ≫
        (closedPointStalkIsoGamma.{u, v} π y hy).hom =
      (closedPointStalkIsoGamma.{u, v} π y' hy').hom := by
  refine NatTrans.ext (funext fun F => ?_)
  let I := (Stacks.EtaleCohomology.smallEtaleInverseImageStalkIso.{v, u} π y).app F
  let I' := (Stacks.EtaleCohomology.smallEtaleInverseImageStalkIso.{v, u} π y').app F
  let Cy := (sheafFiberClosedPointIsoGamma.{u, v} y hy).app
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} π).obj F)
  let Cy' := (sheafFiberClosedPointIsoGamma.{u, v} y' hy').app
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} π).obj F)
  let HSH := (pointSmallEtaleHom y y' a ha).sheafFiber.app
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} π).obj F)
  let HS := (pointSmallEtaleHom (y ≫ π) (y' ≫ π) a (by rw [← Category.assoc, ha])).sheafFiber.app F
  have h1 : HSH ≫ I.hom = I'.hom ≫ HS :=
    smallEtaleInverseImageStalkIso_hom_naturality.{u, v} π y y' a ha F
  have h2 : Cy'.inv ≫ HSH = Cy.inv := congrArg (fun φ => NatTrans.app φ
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} π).obj F))
    (sheafFiberClosedPointIsoGamma_inv_pointSmallEtaleHom.{u, v} y y' hy hy' a ha)
  have k1 : I'.inv ≫ HSH = HS ≫ I.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have k2 : HSH ≫ Cy.hom = Cy'.hom := by
    rw [(Iso.inv_comp_eq Cy').1 h2, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change HS ≫ I.inv ≫ Cy.hom = I'.inv ≫ Cy'.hom
  rw [← reassoc_of% k1, k2]

end ClosedPoint

end AlgebraicGeometry

end

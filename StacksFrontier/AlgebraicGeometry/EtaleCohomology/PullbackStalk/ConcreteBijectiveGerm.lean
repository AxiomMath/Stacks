module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ConstantOfBijectiveGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.EtaleSpecializationGerm

/-!
# Bijective germ maps of a sheaf with values in a concrete category

Let `U` be an object of the small étale site of a scheme `S`, let `A` be a concrete category with
colimits of the size indexing the stalks, and let `F` be a sheaf on the small étale site of `S`
with values in `A`. A family of sections of `F` over `U` has a germ map at every geometric point
of `S` with a lift to `U`.

* If all specialization maps on stalks of `F` are bijective, the germ map of the family is
  bijective at a geometric point of `U` exactly when it is bijective at any generization of it.
* If the family is a morphism `z : E ⟶ F(U)` of `A` and every germ map is bijective, then the
  restriction of `F` to `U` is the constant sheaf with value `E`.

These are the forms of `AlgebraicGeometry.bijective_concreteGerm_iff_of_specializes` and
`AlgebraicGeometry.isConstant_overPullback_of_bijective_germHom` for sheaves with values in a
concrete category, such as sheaves of modules, rather than in sets.

## Main definitions

* `AlgebraicGeometry.constantPresheafHomOfSectionsHom` — the comparison map from the constant
  presheaf with value `E` on the localized site attached to a morphism `E ⟶ F(U)`.

## Main results

* `AlgebraicGeometry.bijective_concreteGerm_lift_iff` — a lift of a geometric point of `S` to `U`
  is a geometric point of the scheme `U`, with the same germ map.
* `AlgebraicGeometry.bijective_concreteGerm_iff_of_specializes` — bijectivity of a germ map is
  invariant along specializations when all specialization maps on stalks are bijective.
* `AlgebraicGeometry.isConstant_overPullback_of_bijective_germHom` — bijectivity of all germ maps
  identifies the restriction of `F` to `U` with the constant sheaf on `E`.

## Implementation notes

The proofs are those of the sheaf-of-sets versions in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PullbackStalk/ConstantOfBijectiveGerm.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PullbackStalk/EtaleSpecializationGerm.lean`, run
through the germ calculus of `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber`, which
needs the forgetful functor of `A` to preserve the filtered colimits indexing the stalks. The
last step identifies the sheafified comparison map as an isomorphism by
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`, whence the hypotheses that `J.W` is local
bijectivity for `A`-valued presheaves and that the forgetful functor reflects isomorphisms.

## References

* [Stacks Project, Tag 0GJ5](https://stacks.math.columbia.edu/tag/0GJ5)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w uA vA u

namespace AlgebraicGeometry

section Specialization

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A : Type uA} [Category.{vA} A] {FC : A → A → Type*} {CC : A → Type w}
  [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
  [HasColimitsOfSize.{u, u} A]

/-- The germ map of a family of sections over `U` depends only on the geometric point of `S` and
on the lift of it to `U`, not on how the two are presented. -/
public theorem bijective_concreteGerm_congr (U : SmallEtale B S hS)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) {M : Type*} (z : M → ToType (P.obj (op U)))
    {s s' : GeometricPoint S} (x : (geometricPointFiber B S hS s).obj U)
    (x' : (geometricPointFiber B S hS s').obj U) (h : s' = s) (hx : HEq x' x) :
    Function.Bijective (fun a : M =>
        (geometricPointSitePoint B S hS s').toPresheafFiber U x' P (z a)) ↔
      Function.Bijective (fun a : M =>
        (geometricPointSitePoint B S hS s).toPresheafFiber U x P (z a)) := by
  subst h
  obtain rfl := eq_of_heq hx
  rfl

/-- A lift to `U` of a geometric point `s` of `S` is the same datum as a geometric point of the
scheme `U` with image `s`, so the two germ maps of a family of sections over `U` agree. -/
public theorem bijective_concreteGerm_lift_iff (U : SmallEtale B S hS)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) {M : Type*} (z : M → ToType (P.obj (op U)))
    (s : GeometricPoint S) (x : (geometricPointFiber B S hS s).obj U) :
    Function.Bijective (fun a : M => (geometricPointSitePoint B S hS
        ((⟨s.residueField, x.1⟩ : GeometricPoint U.obj.left.1).map
          (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨x.1, rfl⟩ P (z a)) ↔
      Function.Bijective (fun a : M =>
        (geometricPointSitePoint B S hS s).toPresheafFiber U x P (z a)) :=
  bijective_concreteGerm_congr B S hS U P z
    (s' := (⟨s.residueField, x.1⟩ : GeometricPoint U.obj.left.1).map
      (B.inclusion.map U.obj.hom)) x ⟨x.1, rfl⟩
    (congrArg (fun m => (⟨s.residueField, m⟩ : GeometricPoint S)) x.2)
    ((Subtype.heq_iff_coe_eq fun v => Iff.of_eq (congrArg
      (fun m => v ≫ B.inclusion.map U.obj.hom = m) x.2)).2 rfl)

/-- If all specialization maps on stalks of a presheaf are bijective, then the map sending an
index to the germ over `U` of the corresponding section is bijective at a geometric point `s` of
`U` exactly when it is bijective at a geometric point `t` of `U` lying over a generization of the
image of `s`. -/
public theorem bijective_concreteGerm_iff_of_specializes (U : SmallEtale B S hS)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ A)
    (hsp : ∀ (r : GeometricPoint S) (σ : GeometricSpecialization B S hS r),
      Function.Bijective (specializationMapOnStalks σ P))
    {M : Type*} (z : M → ToType (P.obj (op U))) (s t : GeometricPoint U.obj.left.1)
    (hts : t.hom default ⤳ s.hom default) :
    Function.Bijective (fun a : M => (geometricPointSitePoint B S hS
        (s.map (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨s.hom, rfl⟩ P (z a)) ↔
      Function.Bijective (fun a : M => (geometricPointSitePoint B S hS
        (t.map (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨t.hom, rfl⟩ P (z a)) := by
  obtain ⟨l, hl, -⟩ := exists_lift_toStrictHenselization_of_specializes B U.obj.left.1
    U.obj.left.property (t.hom default) (s.hom default) hts t s rfl rfl
  have hbase := strictHenselizationSquareMap_comp B U.obj.left.property hS
    (B.inclusion.map U.obj.hom) s
  have hfactor := strictHenselizationSquareMap_comp_strictHenselizationEtaleFactor B S hS U s
  let σ : GeometricSpecialization B S hS (s.map (B.inclusion.map U.obj.hom)) :=
    { target := t.map (B.inclusion.map U.obj.hom)
      lift := l ≫ strictHenselizationSquareMap B U.obj.left.property hS
        (B.inclusion.map U.obj.hom) s
      lift_comp := by
        rw [Category.assoc, hbase, ← Category.assoc, hl, GeometricPoint.map_hom] }
  have hσ : (specializationFiberHom σ).app U ⟨s.hom, rfl⟩ = ⟨t.hom, rfl⟩ := by
    apply Subtype.ext
    rw [specializationFiberHom_app_val]
    change (l ≫ strictHenselizationSquareMap B U.obj.left.property hS
      (B.inclusion.map U.obj.hom) s) ≫ _ = t.hom
    rw [Category.assoc, hfactor, hl]
  have hcomp : (fun a : M => (geometricPointSitePoint B S hS
        (t.map (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨t.hom, rfl⟩ P (z a)) =
      (fun y => specializationMapOnStalks σ P y) ∘
        (fun a : M => (geometricPointSitePoint B S hS
          (s.map (B.inclusion.map U.obj.hom))).toPresheafFiber U ⟨s.hom, rfl⟩ P (z a)) := by
    refine funext fun a => ?_
    have hc := ConcreteCategory.congr_hom
      (ι_comp_specializationMapOnStalks σ P (Functor.elementsMk
        (geometricPointFiber B S hS (s.map (B.inclusion.map U.obj.hom))) U ⟨s.hom, rfl⟩))
      (z a)
    refine Eq.symm ((((CategoryTheory.comp_apply _ _ (z a)).symm.trans hc)).trans
      (congrArg (fun y : (geometricPointFiber B S hS
        (t.map (B.inclusion.map U.obj.hom))).obj U =>
      (geometricPointSitePoint B S hS
        (t.map (B.inclusion.map U.obj.hom))).toPresheafFiber U y P (z a)) hσ))
  rw [hcomp]
  exact (Function.Bijective.of_comp_iff'
    (hsp (s.map (B.inclusion.map U.obj.hom)) σ) _).symm

end Specialization

section Constant

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type uA} [Category.{vA} A] {FC : A → A → Type*} {CC : A → Type w}
  [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
  [HasColimitsOfSize.{u, u} A] [PreservesFilteredColimitsOfSize.{u, u} (forget A)]
  (F : Sheaf (SmallEtale.topology B S hS) A) (U : SmallEtale B S hS)
  {E : A} (z : E ⟶ F.obj.obj (op U))

/-- The comparison map attached to a family `z` of sections of `F` over `U`: on an object `V` of
the localized site it sends an index to the restriction along `V ⟶ U` of the corresponding
section. -/
public def constantPresheafHomOfSectionsHom :
    (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ F.obj where
  app V := z ≫ F.obj.map V.unop.hom.op
  naturality V W f := by
    change 𝟙 E ≫ z ≫ F.obj.map W.unop.hom.op =
      (z ≫ F.obj.map V.unop.hom.op) ≫ F.obj.map f.unop.left.op
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp, ← op_comp, Over.w]

omit [HasColimitsOfSize.{u, u} A] in
/-- The comparison map restricts a section of the family along the structure morphism. -/
public theorem constantPresheafHomOfSectionsHom_app (V : (Over U)ᵒᵖ) :
    (constantPresheafHomOfSectionsHom B S hS F U z).app V = z ≫ F.obj.map V.unop.hom.op :=
  rfl

omit [HasColimitsOfSize.{u, u} A] [PreservesFilteredColimitsOfSize.{u, u} (forget A)] in
/-- The elementwise form of `AlgebraicGeometry.constantPresheafHomOfSectionsHom_app`. -/
public theorem constantPresheafHomOfSectionsHom_app_apply (V : (Over U)ᵒᵖ) (a : ToType E) :
    (constantPresheafHomOfSectionsHom B S hS F U z).app V a =
      F.obj.map V.unop.hom.op (z a) :=
  CategoryTheory.comp_apply z (F.obj.map V.unop.hom.op) a

omit [PreservesFilteredColimitsOfSize.{u, u} (forget A)] in
/-- The germ at a geometric point of `S` lifted to `V` of a restricted section of the family is
the germ at the image lift to `U` of the section itself. -/
public theorem toPresheafFiber_constantPresheafHomOfSectionsHom {r : GeometricPoint S}
    (V : Over U) (y : (geometricPointFiber B S hS r).obj V.left) (a : ToType E) :
    (geometricPointSitePoint B S hS r).toPresheafFiber V.left y F.obj
        ((constantPresheafHomOfSectionsHom B S hS F U z).app (op V) a) =
      (geometricPointSitePoint B S hS r).toPresheafFiber U
        ((geometricPointFiber B S hS r).map V.hom y) F.obj (z a) :=
  (congrArg ((geometricPointSitePoint B S hS r).toPresheafFiber V.left y F.obj)
      (constantPresheafHomOfSectionsHom_app_apply B S hS F U z (op V) a)).trans
    ((geometricPointSitePoint B S hS r).toPresheafFiber_w_apply V.hom y F.obj (z a))

omit [PreservesFilteredColimitsOfSize.{u, u} (forget A)] in
/-- If every germ map of the family is injective, the comparison map from the constant presheaf
is locally injective for the localized topology. -/
public theorem isLocallyInjective_constantPresheafHomOfSectionsHom
    (hz : ∀ (r : GeometricPoint S) (x : (geometricPointFiber B S hS r).obj U),
      Function.Injective fun a : ToType E =>
        (geometricPointSitePoint B S hS r).toPresheafFiber U x F.obj (z a)) :
    Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U)
      (constantPresheafHomOfSectionsHom B S hS F U z) := by
  constructor
  intro V a b hab
  rw [GrothendieckTopology.mem_over_iff]
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  set r := geometricPointOfEtalePoint B S hS V.unop.left x
  set p := geometricPointOfEtalePointLift B S hS V.unop.left x
  have hgerm : (geometricPointSitePoint B S hS r).toPresheafFiber U
        ((geometricPointFiber B S hS r).map V.unop.hom p) F.obj (z a) =
      (geometricPointSitePoint B S hS r).toPresheafFiber U
        ((geometricPointFiber B S hS r).map V.unop.hom p) F.obj (z b) := by
    rw [← toPresheafFiber_constantPresheafHomOfSectionsHom B S hS F U z V.unop p a,
      ← toPresheafFiber_constantPresheafHomOfSectionsHom B S hS F U z V.unop p b]
    exact congrArg ((geometricPointSitePoint B S hS r).toPresheafFiber V.unop.left p F.obj) hab
  obtain rfl : a = b := hz _ _ hgerm
  refine ⟨V.unop.left, 𝟙 _, ?_, ⟨x, by simp⟩⟩
  rw [Sieve.overEquiv_iff]
  simp

/-- If every germ map of the family is surjective, the comparison map from the constant presheaf
is locally surjective for the localized topology. -/
public theorem isLocallySurjective_constantPresheafHomOfSectionsHom
    (hz : ∀ (r : GeometricPoint S) (x : (geometricPointFiber B S hS r).obj U),
      Function.Surjective fun a : ToType E =>
        (geometricPointSitePoint B S hS r).toPresheafFiber U x F.obj (z a)) :
    Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U)
      (constantPresheafHomOfSectionsHom B S hS F U z) := by
  constructor
  intro V c
  rw [GrothendieckTopology.mem_over_iff]
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  set r := geometricPointOfEtalePoint B S hS V.left x
  set p := geometricPointOfEtalePointLift B S hS V.left x
  obtain ⟨e, he⟩ := hz r ((geometricPointFiber B S hS r).map V.hom p)
    ((geometricPointSitePoint B S hS r).toPresheafFiber V.left p F.obj c)
  obtain ⟨W, g, y, hy, heq⟩ :=
    ((geometricPointSitePoint B S hS r).toPresheafFiber_eq_iff' (P := F.obj) V.left p
      ((constantPresheafHomOfSectionsHom B S hS F U z).app (op V) e) c).1
      ((toPresheafFiber_constantPresheafHomOfSectionsHom B S hS F U z V p e).trans he)
  refine ⟨W, g, ?_, ?_⟩
  · rw [Sieve.overEquiv_iff]
    refine ⟨e, ?_⟩
    rw [constantPresheafHomOfSectionsHom_app_apply B S hS F U z]
    change F.obj.map (g ≫ V.hom).op (z e) = F.obj.map g.op c
    rw [op_comp, Functor.map_comp_apply]
    exact (ConcreteCategory.congr_arg (F.obj.map g.op)
      (constantPresheafHomOfSectionsHom_app_apply B S hS F U z (op V) e)).symm.trans heq
  · refine ⟨y.1 default, ?_⟩
    have h1 : y.1 ≫ (SmallEtale.toScheme B S hS).map g = p.1 := congrArg Subtype.val hy
    have h2 : p.1 default = x := geometricPointOfEtalePointLift_base B S hS V.left x
    rw [← h2, ← h1]
    rfl

/-- If every germ map of the family is bijective, the restriction of `F` to `U` is the constant
sheaf with value `E` on the localized site. -/
public theorem isConstant_overPullback_of_bijective_germHom
    [HasWeakSheafify ((SmallEtale.topology B S hS).over U) A]
    [((SmallEtale.topology B S hS).over U).WEqualsLocallyBijective A]
    [((SmallEtale.topology B S hS).over U).HasSheafCompose (forget A)]
    [(forget A).ReflectsIsomorphisms]
    (hz : ∀ (r : GeometricPoint S) (x : (geometricPointFiber B S hS r).obj U),
      Function.Bijective fun a : ToType E =>
        (geometricPointSitePoint B S hS r).toPresheafFiber U x F.obj (z a)) :
    Nonempty ((constantSheaf ((SmallEtale.topology B S hS).over U) A).obj E ≅
      ((SmallEtale.topology B S hS).overPullback A U).obj F) := by
  have hinj := isLocallyInjective_constantPresheafHomOfSectionsHom B S hS F U z
    fun r x => (hz r x).1
  have hsurj := isLocallySurjective_constantPresheafHomOfSectionsHom B S hS F U z
    fun r x => (hz r x).2
  let φ : (constantSheaf ((SmallEtale.topology B S hS).over U) A).obj E ⟶
      ((SmallEtale.topology B S hS).overPullback A U).obj F :=
    ⟨sheafifyLift ((SmallEtale.topology B S hS).over U)
      (constantPresheafHomOfSectionsHom B S hS F U z)
      (((SmallEtale.topology B S hS).overPullback A U).obj F).property⟩
  have hfac : toSheafify ((SmallEtale.topology B S hS).over U)
        ((Functor.const (Over U)ᵒᵖ).obj E) ≫ φ.hom =
      constantPresheafHomOfSectionsHom B S hS F U z :=
    toSheafify_sheafifyLift _ _ _
  have h1 : Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) φ.hom :=
    (Presheaf.comp_isLocallyInjective_iff ((SmallEtale.topology B S hS).over U)
      (toSheafify ((SmallEtale.topology B S hS).over U)
        ((Functor.const (Over U)ᵒᵖ).obj E)) φ.hom).1 (by rwa [hfac])
  have h2 : Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) φ.hom :=
    (Presheaf.comp_isLocallySurjective_iff ((SmallEtale.topology B S hS).over U)
      (toSheafify ((SmallEtale.topology B S hS).over U)
        ((Functor.const (Over U)ᵒᵖ).obj E)) φ.hom).1 (by rwa [hfac])
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨h1, h2⟩
  exact ⟨asIso φ⟩

end Constant

end AlgebraicGeometry

end

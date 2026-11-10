module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientInertia
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsWithEquivariantMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.StackOfTorsors
public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulGroupoidDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective

/-!
# The quotient by an abstract group is a stack in groupoids (Stacks 0371)

Let `S` be a scheme of a big fppf site, let `G` be an abstract group, let `X` be an algebraic
space over `S` and let `ρ : G →* Aut X` be an action of `G` on `X`. Stacks 0371 constructs the
category `[[X/G]]` of `AlgebraicGeometry.AbstractGroupQuotientStack` together with its functor
to `(Sch/S)_fppf`, and asserts that this functor turns `[[X/G]]` into a stack in groupoids.
This file proves that assertion.

Forgetting the equivariant map `φ : P → X` of a triple `(U, P, φ)` is a functor
`[[X/G]] ⥤ 𝒢-Torsors` to the category of torsors under the constant sheaf of groups `𝒢 = G`
of Stacks 04UJ, and it is faithful because a morphism of `[[X/G]]` is a morphism of torsors
subject to a *condition*. The category `𝒢-Torsors` is a stack in groupoids by Stacks 04UK, so
Stacks 0CKJ reduces the assertion to the sheaf condition for the presheaf of pairs
`(x, f : F(x) → h^*y)`, which over `h : V ⟶ U` is the presheaf of equivariant maps
`h^*P → X`; that is a sheaf because `X` is one.

## Main definitions

* `AlgebraicGeometry.AbstractGroupQuotientStack.toTorsors` and
  `AlgebraicGeometry.AbstractGroupQuotientStack.forget`: the torsor underlying an object of
  `[[X/G]]` and the functor `[[X/G]] ⥤ 𝒢-Torsors` forgetting the equivariant map.
* `AlgebraicGeometry.AbstractGroupQuotientStack.ofTotal`: an object of `[[X/G]]` presented by
  a torsor together with an equivariant map of presheaves out of its total space, which is the
  form in which the glued object of a descent datum is produced.
* `AlgebraicGeometry.AbstractGroupQuotientStack.restrict`: the restriction of an object of
  `[[X/G]]` along a morphism of torsors into its torsor, which supplies the cartesian lifts.
* `AlgebraicGeometry.AbstractGroupQuotientStack.totalPresheaf`: the total space of a torsor as
  a presheaf on `(Sch/S)_fppf`, in which the equivariant map of an object is a morphism of
  presheaves.

## Main results

* `AlgebraicGeometry.AbstractGroupQuotientStack.projection_isFiberedInGroupoids`: the functor
  `[[X/G]] ⥤ (Sch/S)_fppf` is fibred in groupoids.
* `AlgebraicGeometry.AbstractGroupQuotientStack.projection_isStack_of_isSheaf`: the functor is
  a stack in the sense of Stacks 026F as soon as `X` is an fppf sheaf.
* `AlgebraicGeometry.AbstractGroupQuotientStack.projection_isStackInGroupoids`: **Stacks
  0371**, the functor is a stack in groupoids over `(Sch/S)_fppf` when `X` is an algebraic
  space over `S`, which is the standing hypothesis of the source.

## Implementation notes

The section universe of the torsors is pinned to `max z (u + 1)`, where `u` is the universe of
the schemes and `z` is a universe parameter of the values of `X`. Two constraints force this.
The reverse stack bridge `CategoryTheory.Functor.isStack_of_isStackInGroupoids` from Stacks
02ZI to Stacks 026F consumes covering families indexed in `max u₁ v₁`, which for the big fppf
site is `u + 1`; and Stacks 04UK bounds the sections of a glued torsor below by the index
universe of the covering. The values of `X` must lie in the same universe as the sections of
the total space of a torsor, since the equivariant maps are glued there.

## References

* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
* [Stacks Project, Tag 04UJ](https://stacks.math.columbia.edu/tag/04UJ)
* [Stacks Project, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK)
* [Stacks Project, Tag 0CKJ](https://stacks.math.columbia.edu/tag/0CKJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe t z w u

/-! ### The constant sheaf of groups is representable

The remark's closing sentence begins by recalling that the constant sheaf `G` on
`(Sch/S)_fppf` is representable by the constant group scheme `G_S` provided the cardinality of
`G` is not too large; that is
`AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme_bigFppf`, whose
smallness hypothesis `Small.{u} G` is the size condition the source alludes to, and which is
recorded here as part of the covering set of the tag. -/

add_to_stacks 0371 "the constant sheaf G is representable by G_S on (Sch/S)_fppf"
  AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme_bigFppf

/-! ### The equivalence with `[[X/G_S]]`

The remark's closing sentence ends by asserting that `[[X/G]]` is equivalent to the `[[X/G_S]]`
of Situation 04WL for the constant group algebraic space `G_S`. That is
`AlgebraicGeometry.nonempty_isEquivalenceOver_abstractGroupQuotientStack` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackEquivalence`, proved
by Stacks 046N: the comparison functor `[[X/G_S]] ⥤ [[X/G]]` is fully faithful, both sides are
stacks, and an object of `[[X/G]]` is fppf locally in the essential image because a torsor under
the constant sheaf has sections fppf locally. -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {G : Type w} [Group G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]

/-- The constant sheaf of groups with value `G` on the big fppf site of `S` itself.
`AlgebraicGeometry.constantGroupSheaf` is its restriction to the localized site at an object
of `(Sch/S)_fppf`, so the two have the same sections and one and the same group acts on the
torsors of all fibres of `[[X/G]]`. -/
abbrev bigConstantGroupSheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type w) [Group G] [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}] :
    SheafOfGroups.{w} (C := BigFppfOver B S hS) (BigFppfOver.topology B S hS) :=
  constantSheafOfGroups (BigFppfOver.topology B S hS) G

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type z} {ρ : G →* Aut X}

namespace AbstractGroupQuotientStack

/-! ### The functor forgetting the equivariant map -/

/-- The torsor underlying an object of `[[X/G]]`, as an object of the category `𝒢-Torsors` of
Stacks 04UJ for the constant sheaf of groups `𝒢` with value `G`. -/
def toTorsors (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) :
    SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G) where
  base := A.base
  torsor := A.torsor
  isTorsor := A.isTorsor

/-- The functor `[[X/G]] ⥤ 𝒢-Torsors` forgetting the equivariant map `φ` of a triple. -/
def forget : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤
    SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G) where
  obj A := A.toTorsors
  map m :=
    { base := Hom.base m
      map := Hom.map m
      map_naturality := Hom.map_naturality m
      map_equivariant := Hom.map_equivariant m
      bijOn_map := Hom.bijOn_map m }

/-- The functor `forget` sends an object of `[[X/G]]` to its underlying torsor. -/
@[simp]
theorem forget_obj (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) :
    (forget (ρ := ρ)).obj A = A.toTorsors :=
  rfl

/-- The total space of the torsor underlying an object of `[[X/G]]` restricts as the total
space of that object does. -/
@[simp]
theorem toTorsors_totalMap (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    {V V' : (BigFppfOver B S hS)ᵒᵖ} (h : V ⟶ V') (p : A.Total V) :
    A.toTorsors.totalMap h p = A.totalMap h p :=
  rfl

/-- The constant sheaf of groups acts on the total space of the torsor underlying an object of
`[[X/G]]` as it does on the total space of that object. -/
@[simp]
theorem toTorsors_totalSmul (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    {V : (BigFppfOver B S hS)ᵒᵖ}
    (γ : (bigConstantGroupSheaf B S hS G).presheaf.obj V) (p : A.Total V) :
    A.toTorsors.totalSmul γ p = A.totalSmul γ p :=
  rfl

/-- The image of a morphism of `[[X/G]]` under the forgetful functor lies over the same
morphism of the big fppf site. -/
@[simp]
theorem forget_map_base {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ} (m : A ⟶ A') :
    SheafOfGroups.Torsors.Hom.base ((forget (ρ := ρ)).map m) = Hom.base m :=
  rfl

/-- The image of a morphism of `[[X/G]]` under the forgetful functor has the same map of
torsors. -/
@[simp]
theorem forget_map_map {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ} (m : A ⟶ A') :
    SheafOfGroups.Torsors.Hom.map ((forget (ρ := ρ)).map m) = Hom.map m :=
  rfl

/-- The functor forgetting the equivariant map is faithful: a morphism of `[[X/G]]` is a
morphism of torsors subject to the condition `φ = φ' ∘ g`, and carries no further data. -/
instance forget_faithful :
    (forget : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤
      SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)).Faithful where
  map_injective {_A _A'} _ _ h :=
    Hom.ext (congrArg SheafOfGroups.Torsors.Hom.base h)
      (congrArg SheafOfGroups.Torsors.Hom.map h)

/-- Forgetting the equivariant map is a functor over `(Sch/S)_fppf`: it is compatible with the
projections of `[[X/G]]` and of `𝒢-Torsors` to the big fppf site. -/
theorem forget_comp_projection :
    (forget : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤
          SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)) ⋙
        SheafOfGroups.Torsors.projection =
      (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ BigFppfOver B S hS) :=
  rfl

/-! ### Objects presented by a map out of the total space -/

/-- The equivariant map of an object of `[[X/G]]`, read on the total space of its torsor, is
compatible with the restriction maps. -/
theorem totalToTarget_naturality (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    {V V' : (BigFppfOver B S hS)ᵒᵖ} (h : V ⟶ V') (p : A.Total V) :
    A.totalToTarget V' (A.totalMap h p) = X.map h (A.totalToTarget V p) :=
  A.toTarget_naturality
    (Over.homMk h.unop : Over.mk (h.unop ≫ p.1) ⟶ Over.mk p.1).op p.2

/-- The equivariant map of an object of `[[X/G]]`, read on the total space of its torsor, is
`G`-equivariant. -/
theorem totalToTarget_totalSmul (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    (V : (BigFppfOver B S hS)ᵒᵖ) (g : G) (p : A.Total V) :
    A.totalToTarget V
        (A.totalSmul (constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G V g) p) =
      (ρ g).asIso.hom.app V (A.totalToTarget V p) :=
  A.toTarget_equivariant (op (Over.mk p.1)) g p.2

/-- An object of `[[X/G]]` presented by a torsor `T` under the constant sheaf of groups with
value `G` together with an equivariant map of presheaves from the total space of `T` to `X`.
This is the form in which the object glued from a descent datum is produced. -/
def ofTotal (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    (τ : ∀ V : (BigFppfOver B S hS)ᵒᵖ, T.Total V → X.obj V)
    (hτ : ∀ {V V' : (BigFppfOver B S hS)ᵒᵖ} (h : V ⟶ V') (p : T.Total V),
      τ V' (T.totalMap h p) = X.map h (τ V p))
    (hτG : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (g : G) (p : T.Total V),
      τ V (T.totalSmul (constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G V g) p) =
        (ρ g).asIso.hom.app V (τ V p)) :
    AbstractGroupQuotientStack.{t} B S hS G X ρ where
  base := T.base
  torsor := T.torsor
  isTorsor := T.isTorsor
  toTarget W s := τ (op W.unop.left) ⟨W.unop.hom, s⟩
  toTarget_naturality {W W'} h s := by
    have h1 := hτ (h.unop.left).op (⟨W.unop.hom, s⟩ : T.Total (op W.unop.left))
    rwa [SheafOfGroups.Torsors.totalMap_mk T (h.unop.left).op (Over.w h.unop).symm
      (h.unop : Over.mk W'.unop.hom ⟶ Over.mk W.unop.hom) rfl s] at h1
  toTarget_equivariant W g s := hτG (op W.unop.left) g ⟨W.unop.hom, s⟩

/-- The torsor underlying `ofTotal T τ hτ hτG` is `T`. -/
@[simp]
theorem toTorsors_ofTotal (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    (τ : ∀ V : (BigFppfOver B S hS)ᵒᵖ, T.Total V → X.obj V) (hτ) (hτG) :
    (ofTotal (ρ := ρ) T τ hτ hτG).toTorsors = T :=
  rfl

/-- The equivariant map of `ofTotal T τ hτ hτG`, read on the total space of `T`, is `τ`. -/
@[simp]
theorem ofTotal_totalToTarget (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    (τ : ∀ V : (BigFppfOver B S hS)ᵒᵖ, T.Total V → X.obj V) (hτ) (hτG)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : T.Total V) :
    (ofTotal (ρ := ρ) T τ hτ hτG).totalToTarget V p = τ V p :=
  rfl

/-- A morphism of `[[X/G]]` built from a morphism of the underlying torsors satisfying
`φ = φ' ∘ g`. -/
def homOfTorsorHom {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    (m : A.toTorsors ⟶ A'.toTorsors)
    (hm : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
      A'.totalToTarget V (SheafOfGroups.Torsors.Hom.map m V p) = A.totalToTarget V p) :
    A ⟶ A' where
  base := SheafOfGroups.Torsors.Hom.base m
  map := SheafOfGroups.Torsors.Hom.map m
  map_naturality := SheafOfGroups.Torsors.Hom.map_naturality m
  map_equivariant := SheafOfGroups.Torsors.Hom.map_equivariant m
  bijOn_map := SheafOfGroups.Torsors.Hom.bijOn_map m
  totalToTarget_comp := hm

/-- The forgetful functor sends `homOfTorsorHom m hm` to the morphism of torsors `m`. -/
@[simp]
theorem forget_map_homOfTorsorHom {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    (m : A.toTorsors ⟶ A'.toTorsors) (hm) :
    (forget (ρ := ρ)).map (homOfTorsorHom m hm) = m :=
  rfl

/-- The restriction of an object of `[[X/G]]` along a morphism of torsors into its torsor: the
same torsor, with the equivariant map composed with the given morphism. -/
def restrict (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)) (m : T ⟶ A.toTorsors) :
    AbstractGroupQuotientStack.{t} B S hS G X ρ :=
  ofTotal T (fun V p => A.totalToTarget V (SheafOfGroups.Torsors.Hom.map m V p))
    (fun h p => by
      rw [SheafOfGroups.Torsors.Hom.map_naturality m h p]
      exact A.totalToTarget_naturality h _)
    (fun V g p => by
      rw [SheafOfGroups.Torsors.Hom.map_equivariant m V _ p]
      exact A.totalToTarget_totalSmul V g _)

/-- The morphism of `[[X/G]]` out of a restriction, lying over the morphism of torsors it was
taken along. -/
def restrictHom (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)) (m : T ⟶ A.toTorsors) :
    A.restrict T m ⟶ A :=
  homOfTorsorHom (A := A.restrict T m) m (fun _ _ => rfl)

/-- The forgetful functor sends `A.restrictHom T m` to the morphism of torsors `m`. -/
@[simp]
theorem forget_map_restrictHom (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)) (m : T ⟶ A.toTorsors) :
    (forget (ρ := ρ)).map (A.restrictHom T m) = m :=
  rfl

/-! ### Condition (1): the projection is fibred in groupoids -/

/-- **Stacks 0371**, condition (1) of Stacks 02ZI. The functor `[[X/G]] ⥤ (Sch/S)_fppf` is
fibred in groupoids: a cartesian lift is obtained by restricting the equivariant map along a
cartesian lift in `𝒢-Torsors` (Stacks 04UK), and a fill-in is unique because it is unique
there and forgetting the equivariant map is faithful. -/
theorem projection_isFiberedInGroupoids :
    (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤
      BigFppfOver B S hS).IsFiberedInGroupoids := by
  have hq := SheafOfGroups.Torsors.projection_isFiberedInGroupoids
    (𝒢 := bigConstantGroupSheaf B S hS G)
  constructor
  · intro V U f A hA
    obtain ⟨T, m, hm⟩ := hq.exists_lift f A.toTorsors hA
    have hd : (SheafOfGroups.Torsors.projection :
        SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G) ⥤ _).obj T = V :=
      @IsHomLift.domain_eq _ _ _ _ SheafOfGroups.Torsors.projection _ _ _ _ f m hm
    have hc : (SheafOfGroups.Torsors.projection :
        SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G) ⥤ _).obj A.toTorsors = U :=
      @IsHomLift.codomain_eq _ _ _ _ SheafOfGroups.Torsors.projection _ _ _ _ f m hm
    exact ⟨A.restrict T m, A.restrictHom T m,
      IsHomLift.of_fac'
        (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ BigFppfOver B S hS)
        f (A.restrictHom T m) hd hc
        (@IsHomLift.fac' _ _ _ _ SheafOfGroups.Torsors.projection _ _ _ _ f m hm)⟩
  · intro A A' A'' m n f hf
    obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ :=
      hq.unique_lift ((forget (ρ := ρ)).map m) ((forget (ρ := ρ)).map n) f hf
    refine ⟨homOfTorsorHom χ ?_, ⟨hχ, ?_⟩, ?_⟩
    · intro V p
      have h1 : SheafOfGroups.Torsors.Hom.map ((forget (ρ := ρ)).map m) V
            (SheafOfGroups.Torsors.Hom.map χ V p) =
          SheafOfGroups.Torsors.Hom.map ((forget (ρ := ρ)).map n) V p :=
        congrFun (congrFun (congrArg SheafOfGroups.Torsors.Hom.map hfac) V) p
      exact ((Hom.totalToTarget_comp m V (SheafOfGroups.Torsors.Hom.map χ V p)).symm.trans
        (congrArg (A.totalToTarget V) h1)).trans (Hom.totalToTarget_comp n V p)
    · exact (forget (ρ := ρ)).map_injective (by rwa [Functor.map_comp])
    · intro a ha
      exact (forget (ρ := ρ)).map_injective
        (huniq ((forget (ρ := ρ)).map a) ⟨ha.1, by rw [← Functor.map_comp, ha.2]⟩)

/-! ### The separatedness half of the sheaf condition of Stacks 0CKJ -/

/-- `AlgebraicGeometry.AbstractGroupQuotientStack.map_eq_of_isHomLift` in the case in which the
target object of the base is the image of the target object, where no identification of it is
needed. -/
private theorem map_eq_of_isHomLift_cod {𝒳 : Type*} [Category 𝒳] {𝒞 : Type*} [Category 𝒞]
    (p : 𝒳 ⥤ 𝒞) {a b : 𝒳} {W : 𝒞} (g : W ⟶ p.obj b) (m : a ⟶ b) (hm : p.IsHomLift g m)
    (ha : p.obj a = W) :
    p.map m = eqToHom ha ≫ g := by
  rw [@IsHomLift.fac' _ _ _ _ p _ _ _ _ g m hm, eqToHom_refl, Category.comp_id]

/-- If a morphism of `[[X/G]]` sends `p` to `q`, then the equivariant maps of its source and target
take `p` and `q` to the same section of `X`. -/
private theorem totalToTarget_eq_of_map_eq {A A' : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    (m : A ⟶ A') {V : (BigFppfOver B S hS)ᵒᵖ} {p : A.Total V} {q : A'.Total V}
    (h : Hom.map m V p = q) : A'.totalToTarget V q = A.totalToTarget V p :=
  h ▸ Hom.totalToTarget_comp m V p

/-- The separatedness half of hypothesis (3) of Stacks 0CKJ for the functor forgetting the
equivariant map: two objects of `[[X/G]]` over `V` whose torsors are identified with one and
the same torsor `y` over `h : V ⟶ U`, and which are locally on `V` identified compatibly with
those identifications, are identified in `[[X/G]]`.

The underlying morphism of torsors exists and is unique because `𝒢-Torsors` is fibred in
groupoids (Stacks 04UK). What has to be proved is that it respects the equivariant maps, and
that is an equality of two sections of `X`, which may be checked on a covering because `X` is a
sheaf: over a member of the covering sieve the given local identification does it. -/
theorem forget_hsep (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (y : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    {V : BigFppfOver B S hS} (h : V ⟶ y.base) (R : Sieve V)
    (hR : R ∈ BigFppfOver.topology B S hS V)
    {x x' : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    (f : x.toTorsors ⟶ y) (f' : x'.toTorsors ⟶ y)
    (hlf : (SheafOfGroups.Torsors.projection :
      SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G) ⥤ _).IsHomLift h f)
    (hlf' : (SheafOfGroups.Torsors.projection :
      SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G) ⥤ _).IsHomLift h f')
    (hloc : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V), R g →
      ∃ (z : AbstractGroupQuotientStack.{t} B S hS G X ρ) (c : z ⟶ x) (c' : z ⟶ x'),
        (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _).IsHomLift g c ∧
        (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _).IsHomLift g c' ∧
        (forget (ρ := ρ)).map c ≫ f = (forget (ρ := ρ)).map c' ≫ f') :
    ∃ e : x ⟶ x',
      (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _).IsHomLift (𝟙 V) e ∧
        (forget (ρ := ρ)).map e ≫ f' = f := by
  classical
  have hqfib := SheafOfGroups.Torsors.projection_isFiberedInGroupoids
    (𝒢 := bigConstantGroupSheaf B S hS G)
  have hX' := (CategoryTheory.isSheaf_iff_isSheaf_of_type _ X).1 hX
  have hxb : x.base = V :=
    @IsHomLift.domain_eq _ _ _ _ SheafOfGroups.Torsors.projection _ _ _ _ h f hlf
  have hxb' : x'.base = V :=
    @IsHomLift.domain_eq _ _ _ _ SheafOfGroups.Torsors.projection _ _ _ _ h f' hlf'
  have hbf : SheafOfGroups.Torsors.Hom.base f = eqToHom hxb ≫ h :=
    map_eq_of_isHomLift_cod SheafOfGroups.Torsors.projection h f hlf hxb
  have hbf' : SheafOfGroups.Torsors.Hom.base f' = eqToHom hxb' ≫ h :=
    map_eq_of_isHomLift_cod SheafOfGroups.Torsors.projection h f' hlf' hxb'
  obtain ⟨χ, ⟨hχb, hχf⟩, -⟩ :=
    hqfib.unique_lift f' f (eqToHom (hxb.trans hxb'.symm)) (by
      change eqToHom (hxb.trans hxb'.symm) ≫ SheafOfGroups.Torsors.Hom.base f' =
        SheafOfGroups.Torsors.Hom.base f
      rw [hbf, hbf']
      simp)
  have hχb' : SheafOfGroups.Torsors.Hom.base χ = eqToHom (hxb.trans hxb'.symm) := hχb
  have hcond : ∀ (W' : BigFppfOver B S hS) (r : x.Total (op W')),
      x'.totalToTarget (op W') (SheafOfGroups.Torsors.Hom.map χ (op W') r) =
        x.totalToTarget (op W') r := by
    intro W' r
    refine (hX' (R.pullback (r.1 ≫ eqToHom hxb))
      ((BigFppfOver.topology B S hS).pullback_stable _ hR)).isSeparatedFor.ext ?_
    intro W g hg
    obtain ⟨z, c, c', hzl, hzl', hze⟩ := hloc (g ≫ r.1 ≫ eqToHom hxb) hg
    have hz : z.base = W :=
      @IsHomLift.domain_eq _ _ _ _
        (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _) _ _ _ _ _ c hzl
    have hcb : Hom.base c = eqToHom hz ≫ (g ≫ r.1 ≫ eqToHom hxb) ≫ eqToHom hxb.symm :=
      @IsHomLift.fac' _ _ _ _ (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _) _ _ _ _
          _ c hzl
    have hcb' : Hom.base c' = eqToHom hz ≫ (g ≫ r.1 ≫ eqToHom hxb) ≫ eqToHom hxb'.symm :=
      @IsHomLift.fac' _ _ _ _ (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _) _ _ _ _
          _ c' hzl'
    -- the morphism of torsors supplied by the stack of torsors is the given local one
    obtain ⟨wit, -, huq⟩ :=
      hqfib.unique_lift f' ((forget (ρ := ρ)).map c' ≫ f') (Hom.base c') rfl
    have hccbase : Hom.base c ≫ SheafOfGroups.Torsors.Hom.base χ = Hom.base c' := by
      have e : (eqToHom hz ≫ (g ≫ r.1 ≫ eqToHom hxb) ≫ eqToHom hxb.symm) ≫
            eqToHom (hxb.trans hxb'.symm) =
          eqToHom hz ≫ (g ≫ r.1 ≫ eqToHom hxb) ≫ eqToHom hxb'.symm := by simp
      rw [hχb', hcb, hcb']
      exact e
    have hccfac : ((forget (ρ := ρ)).map c ≫ χ) ≫ f' = (forget (ρ := ρ)).map c' ≫ f' :=
      (Category.assoc _ _ _).trans
        ((congrArg ((forget (ρ := ρ)).map c ≫ ·) hχf).trans hze)
    have hcc : (forget (ρ := ρ)).map c ≫ χ = (forget (ρ := ρ)).map c' :=
      (huq ((forget (ρ := ρ)).map c ≫ χ) ⟨hccbase, hccfac⟩).trans
        (huq ((forget (ρ := ρ)).map c') ⟨rfl, rfl⟩).symm
    have hmapcc : ∀ (V'' : (BigFppfOver B S hS)ᵒᵖ) (sq : z.Total V''),
        SheafOfGroups.Torsors.Hom.map χ V'' (Hom.map c V'' sq) = Hom.map c' V'' sq :=
      fun V'' sq => congrFun (congrFun (congrArg SheafOfGroups.Torsors.Hom.map hcc) V'') sq
    -- a section of the torsor of `z` over `W` giving the restricted section of the torsor of `x`
    obtain ⟨sq, -, hs⟩ := (Hom.bijOn_map c (op W) (eqToHom hz.symm)).surjOn
      (show (x.totalMap g.op r).1 = eqToHom hz.symm ≫ Hom.base c by
        have e : eqToHom hz.symm ≫
              (eqToHom hz ≫ (g ≫ r.1 ≫ eqToHom hxb) ≫ eqToHom hxb.symm) = g ≫ r.1 := by
          simp
        rw [hcb]
        exact e.symm)
    have hL : X.map g.op
          (x'.totalToTarget (op W') (SheafOfGroups.Torsors.Hom.map χ (op W') r)) =
        z.totalToTarget (op W) sq :=
      (x'.totalToTarget_naturality g.op (SheafOfGroups.Torsors.Hom.map χ (op W') r)).symm.trans
        (totalToTarget_eq_of_map_eq c'
          ((hmapcc (op W) sq).symm.trans
            ((congrArg (SheafOfGroups.Torsors.Hom.map χ (op W)) hs).trans
              (SheafOfGroups.Torsors.Hom.map_naturality χ g.op r))))
    have hRt : X.map g.op (x.totalToTarget (op W') r) = z.totalToTarget (op W) sq :=
      (x.totalToTarget_naturality g.op r).symm.trans (totalToTarget_eq_of_map_eq c hs)
    exact hL.trans hRt.symm
  refine ⟨homOfTorsorHom χ (fun V' r => hcond V'.unop r), ?_, hχf⟩
  refine IsHomLift.of_fac'
    (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _) (𝟙 V)
    (homOfTorsorHom χ (fun V' r => hcond V'.unop r)) hxb hxb' ?_
  have e : eqToHom hxb ≫ 𝟙 V ≫ eqToHom hxb'.symm = eqToHom (hxb.trans hxb'.symm) := by simp
  exact hχb'.trans e.symm

/-- A morphism lying over a morphism of the base whose target object of the base is the image
of the target object, read off from the morphism it records. -/
private theorem isHomLift_of_map_eq {𝒳 : Type*} [Category 𝒳] {𝒞 : Type*} [Category 𝒞]
    (p : 𝒳 ⥤ 𝒞) {a b : 𝒳} {W : 𝒞} (g : W ⟶ p.obj b) (m : a ⟶ b) (ha : p.obj a = W)
    (hm : p.map m = eqToHom ha ≫ g) : p.IsHomLift g m := by
  refine IsHomLift.of_fac' p g m ha rfl ?_
  rw [hm, eqToHom_refl, Category.comp_id]

/-! ### The total space of a torsor as a presheaf -/

/-- The total space of a torsor under the constant sheaf of groups, as a presheaf on the big
fppf site. This is the presentation in which the equivariant map `φ` of an object of `[[X/G]]`
is a morphism of presheaves, and in which such maps are glued. -/
def totalPresheaf (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max u t) where
  obj V := T.Total V
  map h := ↾(T.totalMap h)
  map_id _ := by ext p; exact T.totalMap_id p
  map_comp h k := by ext p; exact (T.totalMap_comp h k p).symm

/-- A morphism of torsors, read on the total-space presheaves. -/
def totalPresheafMap
    {T T' : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)} (m : T ⟶ T') :
    totalPresheaf (B := B) (S := S) (hS := hS) (G := G) T ⟶ totalPresheaf T' where
  app V := ↾(SheafOfGroups.Torsors.Hom.map m V)
  naturality _ _ h := by ext p; exact SheafOfGroups.Torsors.Hom.map_naturality m h p

/-- The translation of the total space of a torsor by an element of `G`, as a morphism of
presheaves; it is one because the sections of the constant sheaf of groups coming from `G` are
compatible with restriction. -/
def totalPresheafSmul (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G)) (g : G) :
    totalPresheaf (B := B) (S := S) (hS := hS) (G := G) T ⟶ totalPresheaf T where
  app V := ↾(fun p =>
    T.totalSmul (constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G V g) p)
  naturality _ _ h := by
    ext p
    exact ((SheafOfGroups.Torsors.totalMap_totalSmul T h _ p).trans
      (congrArg (fun γ => T.totalSmul γ (T.totalMap h p))
        (constantSheafOfGroupsUnit_naturality (BigFppfOver.topology B S hS) G h g))).symm

section Glueing

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max u t)} {ρ : G →* Aut X}

/-- The equivariant map of an object of `[[X/G]]`, as a morphism of presheaves out of the total
space of its torsor. -/
def targetHom (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) :
    totalPresheaf A.toTorsors ⟶ X where
  app V := ↾(A.totalToTarget V)
  naturality _ _ h := by ext p; exact A.totalToTarget_naturality h p

/-! ### The glueing half of the sheaf condition of Stacks 0CKJ -/

/-- The glueing half of hypothesis (3) of Stacks 0CKJ for the functor forgetting the
equivariant map: a family of objects of `[[X/G]]` indexed by a covering sieve of `V`, with
compatible identifications of their torsors with restrictions of a torsor `y` over
`h : V ⟶ U`, is the restriction of a single object of `[[X/G]]` over `V`.

The torsor of that object is the restriction `h^{-1}y` of Stacks 04UK, whose total space is
covered by the total spaces of the given family; the equivariant map out of it is glued from
the given ones, which is possible because `X` is a sheaf, and the glued map is equivariant
because each of the given ones is. -/
theorem forget_hglue (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (y : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    {V : BigFppfOver B S hS} (h : V ⟶ y.base) (R : Sieve V)
    (hR : R ∈ BigFppfOver.topology B S hS V)
    (xs : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V), R g →
      AbstractGroupQuotientStack.{t} B S hS G X ρ)
    (fs : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g), (xs g hg).toTorsors ⟶ y)
    (hfl : ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
      (SheafOfGroups.Torsors.projection :
        SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G) ⥤ _).IsHomLift
        (g ≫ h) (fs g hg))
    (hcompat : ∀ ⦃W W' : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g) (k : W' ⟶ W),
      ∃ c : xs (k ≫ g) (R.downward_closed hg k) ⟶ xs g hg,
        (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _).IsHomLift k c ∧
        (forget (ρ := ρ)).map c ≫ fs g hg = fs (k ≫ g) (R.downward_closed hg k)) :
    ∃ (x₀ : AbstractGroupQuotientStack.{t} B S hS G X ρ) (f₀ : x₀.toTorsors ⟶ y),
      (SheafOfGroups.Torsors.projection :
        SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G) ⥤ _).IsHomLift h f₀ ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g), ∃ c : xs g hg ⟶ x₀,
        (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _).IsHomLift g c ∧
        (forget (ρ := ρ)).map c ≫ f₀ = fs g hg := by
  classical
  have hqfib := SheafOfGroups.Torsors.projection_isFiberedInGroupoids
    (𝒢 := bigConstantGroupSheaf B S hS G)
  have hdd : ∀ (W : BigFppfOver B S hS) (g : W ⟶ V) (hg : R.arrows g), (xs g hg).base = W :=
    fun W g hg => @IsHomLift.domain_eq _ _ _ _ SheafOfGroups.Torsors.projection _ _ _ _ _ _
      (hfl g hg)
  have hbfs : ∀ (W : BigFppfOver B S hS) (g : W ⟶ V) (hg : R.arrows g),
      SheafOfGroups.Torsors.Hom.base (fs g hg) = eqToHom (hdd W g hg) ≫ g ≫ h :=
    fun W g hg => map_eq_of_isHomLift_cod SheafOfGroups.Torsors.projection _ (fs g hg)
      (hfl g hg) (hdd W g hg)
  -- the unique identification of the torsor of each member of the family with a restriction
  -- of `y` over the corresponding arrow of the sieve
  have hcclift : ∀ (W : BigFppfOver B S hS) (g : W ⟶ V) (hg : R.arrows g),
      ∃! c : (xs g hg).toTorsors ⟶ y.pullback h,
        SheafOfGroups.Torsors.Hom.base c = eqToHom (hdd W g hg) ≫ g ∧
          c ≫ y.pullbackHom h = fs g hg := by
    intro W g hg
    refine hqfib.unique_lift (y.pullbackHom h) (fs g hg) (eqToHom (hdd W g hg) ≫ g) ?_
    change (eqToHom (hdd W g hg) ≫ g) ≫
      SheafOfGroups.Torsors.Hom.base (y.pullbackHom h) =
        SheafOfGroups.Torsors.Hom.base (fs g hg)
    rw [hbfs W g hg]
    exact Category.assoc _ _ _
  choose cc hccP hccu using hcclift
  have hccb : ∀ (W : BigFppfOver B S hS) (g : W ⟶ V) (hg : R.arrows g),
      SheafOfGroups.Torsors.Hom.base (cc W g hg) = eqToHom (hdd W g hg) ≫ g :=
    fun W g hg => (hccP W g hg).1
  have hccf : ∀ (W : BigFppfOver B S hS) (g : W ⟶ V) (hg : R.arrows g),
      cc W g hg ≫ y.pullbackHom h = fs g hg := fun W g hg => (hccP W g hg).2
  -- a section of `h^{-1}y` whose base component factors through an arrow of the sieve comes
  -- from the member of the family at that arrow
  have hfromfam : ∀ (W : BigFppfOver B S hS) (g : W ⟶ V) (hg : R.arrows g)
      (q : (y.pullback h).Total (op W)), q.1 = eqToHom (hdd W g hg).symm ≫
        SheafOfGroups.Torsors.Hom.base (cc W g hg) →
      ∃ uu : (xs g hg).Total (op W),
        SheafOfGroups.Torsors.Hom.map (cc W g hg) (op W) uu = q := by
    intro W g hg q hq
    obtain ⟨uu, -, huu⟩ :=
      (SheafOfGroups.Torsors.Hom.bijOn_map (cc W g hg) (op W)
        (eqToHom (hdd W g hg).symm)).surjOn hq
    exact ⟨uu, huu⟩
  -- the identification of a member of the family at a refinement of an arrow of the sieve
  have main : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ) (b : Z.unop ⟶ V) (hb : R.arrows b)
      (W : BigFppfOver B S hS) (g : W ⟶ V) (hg : R.arrows g)
      (uu : (xs g hg).Total Z) (k : Z.unop ⟶ W),
      uu.1 ≫ eqToHom (hdd W g hg) = k → k ≫ g = b →
      ∃ ww : (xs b hb).Total Z,
        SheafOfGroups.Torsors.Hom.map (cc Z.unop b hb) Z ww =
            SheafOfGroups.Torsors.Hom.map (cc W g hg) Z uu ∧
          ww.1 = eqToHom (hdd Z.unop b hb).symm ∧
            (xs b hb).totalToTarget Z ww = (xs g hg).totalToTarget Z uu := by
    intro Z b hb W g hg uu k hk hkb
    subst hkb
    obtain rfl : hb = R.downward_closed hg k := rfl
    obtain ⟨c₁, hc₁l, hc₁f⟩ := hcompat g hg k
    have hc₁b : Hom.base c₁ = eqToHom (hdd Z.unop (k ≫ g) (R.downward_closed hg k)) ≫ k ≫
        eqToHom (hdd W g hg).symm :=
      @IsHomLift.fac' _ _ _ _ (projection : AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤ _) _ _ _ _
          k c₁ hc₁l
    obtain ⟨ww, hww1, hww2⟩ := (Hom.bijOn_map c₁ Z
        (eqToHom (hdd Z.unop (k ≫ g) (R.downward_closed hg k)).symm)).surjOn
      (show uu.1 = eqToHom (hdd Z.unop (k ≫ g) (R.downward_closed hg k)).symm ≫ Hom.base c₁ by
        have e : eqToHom (hdd Z.unop (k ≫ g) (R.downward_closed hg k)).symm ≫
              (eqToHom (hdd Z.unop (k ≫ g) (R.downward_closed hg k)) ≫ k ≫
                eqToHom (hdd W g hg).symm) = k ≫ eqToHom (hdd W g hg).symm := by
          simp
        have e2 : uu.1 = k ≫ eqToHom (hdd W g hg).symm := by rw [← hk]; simp
        rw [hc₁b]
        exact e2.trans e.symm)
    have hceq : cc Z.unop (k ≫ g) (R.downward_closed hg k) =
        (forget (ρ := ρ)).map c₁ ≫ cc W g hg := by
      refine (hccu Z.unop (k ≫ g) (R.downward_closed hg k)
        ((forget (ρ := ρ)).map c₁ ≫ cc W g hg) ⟨?_, ?_⟩).symm
      · have e : (eqToHom (hdd Z.unop (k ≫ g) (R.downward_closed hg k)) ≫ k ≫
                eqToHom (hdd W g hg).symm) ≫ (eqToHom (hdd W g hg) ≫ g) =
            eqToHom (hdd Z.unop (k ≫ g) (R.downward_closed hg k)) ≫ k ≫ g := by
          simp
        change Hom.base c₁ ≫ SheafOfGroups.Torsors.Hom.base (cc W g hg) = _
        rw [hc₁b, hccb W g hg]
        exact e
      · exact (Category.assoc _ _ _).trans
          ((congrArg ((forget (ρ := ρ)).map c₁ ≫ ·) (hccf W g hg)).trans hc₁f)
    refine ⟨ww, ?_, hww1, ?_⟩
    · rw [hceq]
      change SheafOfGroups.Torsors.Hom.map (cc W g hg) Z (Hom.map c₁ Z ww) = _
      exact congrArg (SheafOfGroups.Torsors.Hom.map (cc W g hg) Z) hww2
    · exact (totalToTarget_eq_of_map_eq c₁ hww2).symm
  -- compatibility: two members of the family agreeing on a section of `h^{-1}y` agree there
  have hphi : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ)
      (i j : (W : BigFppfOver B S hS) × {g : W ⟶ V // R.arrows g})
      (uu : (xs i.2.1 i.2.2).Total Z) (vv : (xs j.2.1 j.2.2).Total Z),
      SheafOfGroups.Torsors.Hom.map (cc i.1 i.2.1 i.2.2) Z uu =
          SheafOfGroups.Torsors.Hom.map (cc j.1 j.2.1 j.2.2) Z vv →
        (xs i.2.1 i.2.2).totalToTarget Z uu = (xs j.2.1 j.2.2).totalToTarget Z vv := by
    intro Z i j uu vv huv
    have hb1 : R.arrows ((uu.1 ≫ eqToHom (hdd i.1 i.2.1 i.2.2)) ≫ i.2.1) :=
      R.downward_closed i.2.2 _
    have e1 : (SheafOfGroups.Torsors.Hom.map (cc i.1 i.2.1 i.2.2) Z uu).1 =
        (uu.1 ≫ eqToHom (hdd i.1 i.2.1 i.2.2)) ≫ i.2.1 :=
      (SheafOfGroups.Torsors.Hom.fst_map (cc i.1 i.2.1 i.2.2) uu).trans
        ((congrArg (uu.1 ≫ ·) (hccb i.1 i.2.1 i.2.2)).trans (Category.assoc _ _ _).symm)
    have e2 : (SheafOfGroups.Torsors.Hom.map (cc j.1 j.2.1 j.2.2) Z vv).1 =
        (vv.1 ≫ eqToHom (hdd j.1 j.2.1 j.2.2)) ≫ j.2.1 :=
      (SheafOfGroups.Torsors.Hom.fst_map (cc j.1 j.2.1 j.2.2) vv).trans
        ((congrArg (vv.1 ≫ ·) (hccb j.1 j.2.1 j.2.2)).trans (Category.assoc _ _ _).symm)
    have e3 : (SheafOfGroups.Torsors.Hom.map (cc i.1 i.2.1 i.2.2) Z uu).1 =
        (SheafOfGroups.Torsors.Hom.map (cc j.1 j.2.1 j.2.2) Z vv).1 := by rw [huv]
    have hbb : (vv.1 ≫ eqToHom (hdd j.1 j.2.1 j.2.2)) ≫ j.2.1 =
        (uu.1 ≫ eqToHom (hdd i.1 i.2.1 i.2.2)) ≫ i.2.1 := e2.symm.trans (e3.symm.trans e1)
    obtain ⟨w₁, hw₁a, hw₁b, hw₁c⟩ := main Z _ hb1 i.1 i.2.1 i.2.2 uu _ rfl rfl
    obtain ⟨w₂, hw₂a, hw₂b, hw₂c⟩ := main Z _ hb1 j.1 j.2.1 j.2.2 vv _ rfl hbb
    have hw : w₁ = w₂ :=
      (SheafOfGroups.Torsors.Hom.bijOn_map (cc Z.unop _ hb1) Z
        (eqToHom (hdd Z.unop _ hb1).symm)).injOn hw₁b hw₂b
        (hw₁a.trans (huv.trans hw₂a.symm))
    exact hw₁c.symm.trans ((congrArg ((xs _ hb1).totalToTarget Z) hw).trans hw₂c)
  -- the total spaces of the family cover the total space of `h^{-1}y`
  have hcover : ∀ (Z : BigFppfOver B S hS)
      (q : (totalPresheaf (y.pullback h)).obj (op Z)),
      (Space.familyImage (fun i : (W : BigFppfOver B S hS) × {g : W ⟶ V // R.arrows g} =>
          totalPresheafMap (cc i.1 i.2.1 i.2.2))).sieveOfSection q ∈
        BigFppfOver.topology B S hS Z := by
    intro Z q
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).pullback_stable q.1 hR)
    intro W g hg
    obtain ⟨uu, huu⟩ := hfromfam W (g ≫ q.1) hg ((y.pullback h).totalMap g.op q) (by
      have e : eqToHom (hdd W (g ≫ q.1) hg).symm ≫
          (eqToHom (hdd W (g ≫ q.1) hg) ≫ (g ≫ q.1)) = g ≫ q.1 := by simp
      rw [hccb W (g ≫ q.1) hg]
      exact e.symm)
    exact ⟨⟨W, ⟨g ≫ q.1, hg⟩⟩, uu, huu⟩
  obtain ⟨ψ, hψ, -⟩ := Space.glueHom (BigFppfOver.topology B S hS)
    (fun i : (W : BigFppfOver B S hS) × {g : W ⟶ V // R.arrows g} =>
      totalPresheafMap (cc i.1 i.2.1 i.2.2)) hcover hX
    (fun i => targetHom (xs i.2.1 i.2.2)) (fun Z i j uu vv huv => hphi Z i j uu vv huv)
  have hψ' : ∀ (i : (W : BigFppfOver B S hS) × {g : W ⟶ V // R.arrows g})
      (V' : (BigFppfOver B S hS)ᵒᵖ) (uu : (xs i.2.1 i.2.2).Total V'),
      ψ.app V' (SheafOfGroups.Torsors.Hom.map (cc i.1 i.2.1 i.2.2) V' uu) =
        (xs i.2.1 i.2.2).totalToTarget V' uu :=
    fun i V' uu => ConcreteCategory.congr_hom (NatTrans.congr_app (hψ i) V') uu
  -- the glued map is equivariant, checked on the covering family
  have hequiv : ∀ (V' : (BigFppfOver B S hS)ᵒᵖ) (g : G) (q : (y.pullback h).Total V'),
      ψ.app V' ((y.pullback h).totalSmul
          (constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G V' g) q) =
        (ρ g).asIso.hom.app V' (ψ.app V' q) := by
    intro V' g q
    have key : totalPresheafSmul (y.pullback h) g ≫ ψ = ψ ≫ (ρ g).asIso.hom := by
      refine Space.hom_ext_of_familyImage_cover (BigFppfOver.topology B S hS)
        (fun i : (W : BigFppfOver B S hS) × {g : W ⟶ V // R.arrows g} =>
          totalPresheafMap (cc i.1 i.2.1 i.2.2)) hcover hX _ _ ?_
      intro i
      ext V'' uu
      change ψ.app V'' ((y.pullback h).totalSmul _
          (SheafOfGroups.Torsors.Hom.map (cc i.1 i.2.1 i.2.2) V'' uu)) =
        (ρ g).asIso.hom.app V'' (ψ.app V'' (SheafOfGroups.Torsors.Hom.map
          (cc i.1 i.2.1 i.2.2) V'' uu))
      rw [← SheafOfGroups.Torsors.Hom.map_equivariant (cc i.1 i.2.1 i.2.2) V'' _ uu]
      exact (hψ' i V'' _).trans
        (((xs i.2.1 i.2.2).totalToTarget_totalSmul V'' g uu).trans
          (congrArg (fun zz => (ρ g).asIso.hom.app V'' zz) (hψ' i V'' uu).symm))
    exact ConcreteCategory.congr_hom (NatTrans.congr_app key V') q
  refine ⟨ofTotal (y.pullback h) (fun V' q => ψ.app V' q)
      (fun hh q => ConcreteCategory.congr_hom (ψ.naturality hh) q) hequiv,
    y.pullbackHom h, SheafOfGroups.Torsors.isHomLift_of_base (y.pullbackHom h) rfl, ?_⟩
  intro W g hg
  refine ⟨homOfTorsorHom (cc W g hg) (fun V' uu => hψ' ⟨W, ⟨g, hg⟩⟩ V' uu), ?_, hccf W g hg⟩
  refine isHomLift_of_map_eq _ _ _ ?_ ?_
  · exact hdd W g hg
  · exact hccb W g hg

end Glueing

/-! ### The quotient is a stack in groupoids -/

section IsStack

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max t (u + 1))} {ρ : G →* Aut X}

/-- The functor `[[X/G]] ⥤ (Sch/S)_fppf` is a stack in the sense of Stacks 026F as soon as `X`
is an fppf sheaf, which is the only consequence of `X` being an algebraic space that the
assertion of Stacks 0371 uses.

The proof is Stacks 0CKJ applied to the faithful functor
`AlgebraicGeometry.AbstractGroupQuotientStack.forget` forgetting the equivariant map, whose
target is a stack by Stacks 04UK read through the reverse stack bridge
`CategoryTheory.Functor.isStack_of_isStackInGroupoids`; the two halves of the sheaf condition
it asks for are `AlgebraicGeometry.AbstractGroupQuotientStack.forget_hsep` and
`AlgebraicGeometry.AbstractGroupQuotientStack.forget_hglue`. -/
theorem projection_isStack_of_isSheaf
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    (projection : AbstractGroupQuotientStack.{max t (u + 1)} B S hS G X ρ ⥤
        BigFppfOver B S hS).IsStack (BigFppfOver.topology B S hS) := by
  have hp : (projection : AbstractGroupQuotientStack.{max t (u + 1)} B S hS G X ρ ⥤
      BigFppfOver B S hS).IsFiberedInGroupoids := projection_isFiberedInGroupoids
  have hqfib : (SheafOfGroups.Torsors.projection :
      SheafOfGroups.Torsors.{max t (u + 1)} (bigConstantGroupSheaf B S hS G) ⥤
        BigFppfOver B S hS).IsFiberedInGroupoids :=
    SheafOfGroups.Torsors.projection_isFiberedInGroupoids
  have hqgpd : Functor.IsStackInGroupoids.{u + 1}
      (SheafOfGroups.Torsors.projection :
        SheafOfGroups.Torsors.{max t (u + 1)} (bigConstantGroupSheaf B S hS G) ⥤
          BigFppfOver B S hS) (BigFppfOver.topology B S hS) :=
    SheafOfGroups.Torsors.projection_isStackInGroupoids
  have _ : CategoryTheory.Limits.HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : (SheafOfGroups.Torsors.projection :
      SheafOfGroups.Torsors.{max t (u + 1)} (bigConstantGroupSheaf B S hS G) ⥤
        BigFppfOver B S hS).IsFibered := hqfib.isFibered
  have hqst : (SheafOfGroups.Torsors.projection :
      SheafOfGroups.Torsors.{max t (u + 1)} (bigConstantGroupSheaf B S hS G) ⥤
        BigFppfOver B S hS).IsStack (BigFppfOver.topology B S hS) :=
    Functor.isStack_of_isStackInGroupoids hqgpd
  exact Functor.isStack_of_faithful_of_isSheaf hp hqfib forget_comp_projection hqst
    (fun _ => inferInstance)
    (fun y _ h R hR _ _ f f' hlf hlf' hloc => forget_hsep hX y h R hR f f' hlf hlf' hloc)
    (fun y _ h R hR xs fs hfl hcompat => forget_hglue hX y h R hR xs fs hfl hcompat)

/-- **Stacks 0371.** For an algebraic space `X` over `S` with an action `ρ : G →* Aut X` of an
abstract group `G`, the functor `[[X/G]] ⥤ (Sch/S)_fppf` of
`AlgebraicGeometry.AbstractGroupQuotientStack.projection` turns `[[X/G]]` into a stack in
groupoids over the big fppf site of `S`.

This is the assertion of the remark, under exactly its standing hypothesis that `X` is an
algebraic space over `S`: nothing beyond the sheaf condition for `X` is used, and the three
conditions of Stacks 02ZI are proved outright, with the stack property of the torsors under
the constant sheaf of groups supplied by Stacks 04UK rather than assumed. -/
@[stacks 0371 "[[X/G]] is a stack in groupoids over (Sch/S)_fppf"]
theorem projection_isStackInGroupoids
    (hX : Space.IsAlgebraicSpaceULift.{max t (u + 1)} B S hS X) :
    Functor.IsStackInGroupoids.{w}
      (projection : AbstractGroupQuotientStack.{max t (u + 1)} B S hS G X ρ ⥤
        BigFppfOver B S hS) (BigFppfOver.topology B S hS) :=
  (projection_isStack_of_isSheaf hX.isSheaf).isStackInGroupoids projection_isFiberedInGroupoids

end IsStack

/-- The statement that every torsor under the constant sheaf of groups with value `G` has an
algebraic space as its total space.

An object of `[[X/G_S]]` carries algebraicity of the total space of its torsor as a field, while
the torsor of an object of `[[X/G]]` is an arbitrary sheaf. The equivalence of the two in the
last clause of Stacks 0371 is proved through Stacks 046N
(`AlgebraicGeometry.nonempty_isEquivalenceOver_abstractGroupQuotientStack`), which only needs
local essential surjectivity, so it does not go through this statement. -/
abbrev IsAlgebraicTotalSpaceOfConstantSheafTorsor [Small.{u} G] : Prop :=
  ∀ T : SheafOfGroups.Torsors.{max t (u + 1)} (bigConstantGroupSheaf B S hS G),
    Space.IsAlgebraicSpaceULift.{max t (u + 1)} B S hS (totalPresheaf T)

end AbstractGroupQuotientStack

end AlgebraicGeometry

end

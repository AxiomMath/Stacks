module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientInertiaIsStack
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientInertiaLocalTranslation
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.CategoryTheory.Sites.Stackification.Coproduct
import StacksCore.Tactic.StacksAttribute

/-!
# The inertia stack of the quotient by a commutative group (Stacks 0374)

Let `S` be a scheme, let `G` be a commutative group, let `Y → S` be a scheme over `S` with an
action `a : G →* Aut_S(Y)` of `G`, and for `g ∈ G` let `Y^g = Y ×_{(1, 1), Y ×_S Y, (g, 1)} Y` be
the fixed-point scheme of `g` (`AlgebraicGeometry.fixedScheme`). Stacks 0374 asserts that the
inertia stack of `[Y/G]` is
`I_{[Y/G]} = ∐_{g ∈ G} [Y^g/G]`,
and closes with "We omit showing that this is an equivalence". This file proves it.

## The coproduct

The coproduct in the formula is the coproduct of *stacks* over `(Sch/S)_fppf`
(`CategoryTheory.Functor.StackCoproduct`, the stackification of the disjoint union). It cannot
be read as the plain disjoint union `Σ g, [Y^g/G]` of categories: that disjoint union is not
equivalent to `I_{[Y/G]}`. For instance, if `G` has two elements `g ≠ h`, `Y = S` with the
trivial action and `T = T₁ ⊔ T₂` is a disjoint union of two nonempty objects of the site, the
trivial torsor over `T` with the automorphism which is multiplication by `g` over `T₁` and by `h`
over `T₂` is an object of `I_{[Y/G]}` over `T` lying in no single summand; and over the empty
scheme the disjoint union has one object for each `g`, which are pairwise not isomorphic,
whereas every stack has only one object up to isomorphism there. The source's own argument —
"`α` is, locally in the fppf topology over `T`, given by multiplication by some element `g` of
`G`" — is exactly what produces an object of the stack coproduct, and not of the disjoint union.

## Main results

* `AlgebraicGeometry.inertia_equivalence_stackCoproduct`: **Stacks 0374.** There is an
  equivalence over `(Sch/S)_fppf` from the coproduct of stacks `∐_{g ∈ G} [Y^g/G]` to the
  inertia stack `I_{[Y/G]}` whose restriction to the `g`-th summand is the canonical functor
  `[Y^g/G] ⥤ I_{[Y/G]}` of the source (`AlgebraicGeometry.fixedQuotientToInertia`: a torsor `P`
  with an equivariant map to `Y^g` goes to `P` with the composite map to `Y` and the automorphism
  given by multiplication by `g`).

## Implementation notes

The ingredients are the recognition criterion
`CategoryTheory.Functor.exists_isEquivalenceOver_stackCoproduct` and the following facts.

* `I_{[Y/G]}` is a stack in groupoids: `[Y/G]` is a stack because the functor of points of `Y`
  is an fppf sheaf (`AlgebraicGeometry.AbstractGroupQuotientStack.projection_isStack`), and the
  inertia of a stack is a stack (`CategoryTheory.RelativeInertia.isStack_toBase`).
* The canonical functor `[Y^g/G] ⥤ I_{[Y/G]}` is fully faithful: a morphism of `[Y/G]` between
  objects coming from `Y^g` commutes with multiplication by `g` because it is equivariant, and is
  compatible with the maps to `Y^g` because `Y^g → Y` is a monomorphism.
* Distinct summands are disjoint: a morphism from the image of `[Y^g/G]` to the image of `[Y^h/G]`
  over `T` forces the sections of the constant sheaf attached to `g` and to `h` to agree wherever
  the torsor has a section, hence, the unit of sheafification being locally injective, `T` to be
  covered by the empty sieve when `g ≠ h`.
* Every object of `I_{[Y/G]}` is locally in the image of some summand: its automorphism is
  locally multiplication by some `g ∈ G`
  (`AlgebraicGeometry.exists_covering_auto_eq_translation`), and an object whose automorphism is
  multiplication by `g` comes from `[Y^g/G]` because its map to `Y` then factors through `Y^g`.

The group `G` lives in a universe at least that of the objects of the site, which is where the
constant sheaf of groups is the sheafification of the constant presheaf with its unit locally
injective (`AlgebraicGeometry.wEqualsLocallyBijective_grpCat`), and the torsors have sections in a
universe at least that of the objects of the site, which is where `[Y/G]` is a stack. Both are
choices of universes only: the sheafification and the stack are then the ones the source means.

## References

* [Stacks Project, Tag 0374](https://stacks.math.columbia.edu/tag/0374)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe t v u

/-- Sheaves of groups with values in a universe at least that of the objects of the big fppf site
of `S` can be sheafified. -/
instance bigFppfOver_hasWeakSheafify_grpCat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{max (u + 1) v} :=
  have := hasSheafify_grpCat.{u, v} (BigFppfOver.topology B S hS)
  inferInstance

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {G : Type (max (u + 1) v)} [CommGroup G]

/-- Two elements of `G` whose sections of the constant sheaf of groups agree over an object of the
site are equal, or that object is covered by the empty sieve. -/
lemma bot_mem_of_constantSheafOfGroupsUnit_eq {W : BigFppfOver B S hS} {g h : G} (hgh : g ≠ h)
    (e : constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G (op W) g =
      constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G (op W) h) :
    (⊥ : Sieve W) ∈ BigFppfOver.topology B S hS W := by
  have := wEqualsLocallyBijective_grpCat.{u, v} (BigFppfOver.topology B S hS)
  have hmem := Presheaf.equalizerSieve_mem (BigFppfOver.topology B S hS)
    (toSheafify (BigFppfOver.topology B S hS)
      ((Functor.const (BigFppfOver B S hS)ᵒᵖ).obj (GrpCat.of G))) (X := op W) g h e
  refine (BigFppfOver.topology B S hS).superset_covering (fun Z k hk => ?_) hmem
  exact hgh hk

end

open AbstractGroupQuotientStack

section Scheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : Type (max (u + 1) v)) [CommGroup G] (Y : Over S) (a : G →* Aut Y)

/-- The structure functor `I_{[Y/G]} ⥤ (Sch/S)_fppf` of the inertia stack of `[Y/G]`. -/
abbrev schemeInertiaProj :
    AbsoluteInertia (schemeQuotientProjection.{t} B S hS G Y a) ⥤ BigFppfOver B S hS :=
  relativeInertiaStruct (schemeQuotientProjection.{t} B S hS G Y a)
    (schemeQuotientProjection.{t} B S hS G Y a)

variable {B S hS G Y a}

/-- The canonical functor `[Y^g/G] ⥤ I_{[Y/G]}` is faithful. -/
instance fixedQuotientToInertia_faithful (g : G) :
    (fixedQuotientToInertia.{t} B S hS G Y a g).Faithful where
  map_injective {_ _ m m'} h := by
    have h1 := congrArg RelativeInertiaHom.hom h
    have hb := congrArg (fun k => Hom.base k) h1
    have hm := congrArg (fun k => Hom.map k) h1
    exact Hom.ext hb hm

/-- The canonical functor `[Y^g/G] ⥤ I_{[Y/G]}` is full. -/
instance fixedQuotientToInertia_full (g : G) :
    (fixedQuotientToInertia.{t} B S hS G Y a g).Full where
  map_surjective {A A'} f :=
    ⟨{ base := f.hom.base
       map := f.hom.map
       map_naturality := f.hom.map_naturality
       map_equivariant := f.hom.map_equivariant
       bijOn_map := f.hom.bijOn_map
       totalToTarget_comp := fun V p =>
         fixedScheme_hom_ext (φ := A'.totalToTarget V (f.hom.map V p))
           (ψ := A.totalToTarget V p) (f.hom.totalToTarget_comp V p) },
     RelativeInertiaHom.ext rfl⟩

/-- **Distinct summands are disjoint.** A morphism in `I_{[Y/G]}` from the image of an object of
`[Y^g/G]` to the image of an object of `[Y^h/G]` with `g ≠ h` exists only over an object of the
site covered by the empty sieve: at every section of the torsor, multiplication by `g` and by `h`
agree, so the sections of the constant sheaf attached to `g` and `h` agree wherever the torsor has
sections, which is locally everywhere. -/
lemma fixedQuotientToInertia_disjoint {g h : G} (hgh : g ≠ h)
    (A : fixedSchemeQuotient.{t} B S hS G Y a g) (A' : fixedSchemeQuotient.{t} B S hS G Y a h)
    (m : (fixedQuotientToInertia.{t} B S hS G Y a g).obj A ⟶
      (fixedQuotientToInertia.{t} B S hS G Y a h).obj A') :
    (⊥ : Sieve A.base) ∈ BigFppfOver.topology B S hS A.base := by
  have key : ∀ (W : BigFppfOver B S hS) (_ : A.Total (op W)),
      (⊥ : Sieve W) ∈ BigFppfOver.topology B S hS W := by
    intro W p
    have e1 : m.hom.map (op W) (A.translationMap g (op W) p) =
        ((fixedSchemeQuotientToQuotient.{t} B S hS G Y a h).obj A').translationMap h (op W)
          (m.hom.map (op W) p) :=
      (congrFun (congrFun (congrArg Hom.map m.comm) (op W)) p).symm
    have e2 : m.hom.map (op W) (A.translationMap g (op W) p) =
        ((fixedSchemeQuotientToQuotient.{t} B S hS G Y a h).obj A').translationMap g (op W)
          (m.hom.map (op W) p) :=
      m.hom.map_equivariant (op W) _ p
    refine bot_mem_of_constantSheafOfGroupsUnit_eq hgh
      ((existsUnique_totalSmul_eq _ (m.hom.map (op W) p)
        (((fixedSchemeQuotientToQuotient.{t} B S hS G Y a h).obj A').translationMap g (op W)
          (m.hom.map (op W) p)) rfl).unique rfl (e1.symm.trans e2))
  obtain ⟨R, hR, hsec⟩ := A.isTorsor (Over.mk (𝟙 A.base))
  have hR₀ : Sieve.overEquiv _ R ∈ (BigFppfOver.topology B S hS) A.base :=
    ((BigFppfOver.topology B S hS).mem_over_iff R).mp hR
  refine (BigFppfOver.topology B S hS).transitive hR₀ _ (fun V f hf => ?_)
  have hk : R (Over.homMk f (by simp) : (Over.mk f : Over A.base) ⟶ Over.mk (𝟙 A.base)) := by
    rw [← (Sieve.overEquiv (Over.mk (𝟙 A.base))).symm_apply_apply R]
    exact hf
  obtain ⟨s⟩ := hsec hk
  have hV := key V ⟨f, s⟩
  refine (BigFppfOver.topology B S hS).superset_covering (fun Z k hk => ?_) hV
  exact hk.elim

/-- A morphism of `[Y/G]` lying over a morphism `a` of the site to the base of its target records
`a`, conjugated by the identification of the base of its source. -/
lemma base_of_isHomLift_tgt {A A' : schemeQuotient.{t} B S hS G Y a} {V : BigFppfOver B S hS}
    (f : V ⟶ A'.base) (m : A ⟶ A') (hm : projection.IsHomLift f m) (hA : A.base = V) :
    m.base = eqToHom hA ≫ f := by
  rw [base_of_isHomLift f m hm hA rfl]
  simp

/-- The source's "`φ ∘ α = φ`": if the automorphism of an object of `I_{[Y/G]}` is multiplication
by `g`, then its equivariant map to `Y` is fixed by `g`. -/
lemma toTarget_fixed_of_auto {g : G}
    (Z : AbsoluteInertia (schemeQuotientProjection.{t} B S hS G Y a))
    (hZ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (p : Z.obj.Total W),
      Z.auto.hom.map W p = Z.obj.translationMap g W p)
    (W : (Over Z.obj.base)ᵒᵖ) (s : Z.obj.torsor.presheaf.obj W) :
    Z.obj.toTarget W s ≫ (a g).hom = Z.obj.toTarget W s := by
  have h1 := Z.auto.hom.totalToTarget_comp (op W.unop.left)
    (⟨W.unop.hom, s⟩ : Z.obj.Total (op W.unop.left))
  rw [hZ (op W.unop.left) (⟨W.unop.hom, s⟩ : Z.obj.Total (op W.unop.left))] at h1
  exact (Z.obj.toTarget_equivariant W g s).symm.trans h1

/-- An object of `I_{[Y/G]}` whose automorphism is multiplication by `g`, as an object of
`[Y^g/G]`: its equivariant map to `Y` factors through `Y^g`. -/
def fixedSchemePull {g : G} (Z : AbsoluteInertia (schemeQuotientProjection.{t} B S hS G Y a))
    (hZ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (p : Z.obj.Total W),
      Z.auto.hom.map W p = Z.obj.translationMap g W p) :
    fixedSchemeQuotient.{t} B S hS G Y a g where
  base := Z.obj.base
  torsor := Z.obj.torsor
  isTorsor := Z.obj.isTorsor
  toTarget W s := fixedSchemeLift (Z.obj.toTarget W s) (toTarget_fixed_of_auto Z hZ W s)
  toTarget_naturality h s := fixedScheme_hom_ext ((fixedSchemeLift_comp_incl _ _).trans
    ((Z.obj.toTarget_naturality h s).trans
      ((congrArg (_ ≫ ·) (fixedSchemeLift_comp_incl _ _)).symm.trans (Category.assoc _ _ _).symm)))
  toTarget_equivariant W g' s := fixedScheme_hom_ext ((fixedSchemeLift_comp_incl _ _).trans
    ((Z.obj.toTarget_equivariant W g' s).trans
      (((congrArg (· ≫ (a g').hom) (fixedSchemeLift_comp_incl _ _)).symm.trans
        (Category.assoc _ _ _)).trans
        ((congrArg (_ ≫ ·) (fixedSchemeMap_comp_incl Y a g g')).symm.trans
          (Category.assoc _ _ _).symm))))

/-- The identity of the torsor, as a morphism of `[Y/G]` from the image of the object of `[Y^g/G]`
attached to an object of `I_{[Y/G]}` whose automorphism is multiplication by `g` to the underlying
object. -/
def fixedSchemePullObjHom {g : G}
    (Z : AbsoluteInertia (schemeQuotientProjection.{t} B S hS G Y a))
    (hZ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (p : Z.obj.Total W),
      Z.auto.hom.map W p = Z.obj.translationMap g W p) :
    (fixedSchemeQuotientToQuotient.{t} B S hS G Y a g).obj (fixedSchemePull Z hZ) ⟶ Z.obj where
  base := 𝟙 Z.obj.base
  map := fun _ p => p
  map_naturality := fun _ _ => rfl
  map_equivariant := fun _ _ _ => rfl
  bijOn_map := fun _ c => ⟨fun _ hp => hp.trans (Category.comp_id c).symm,
    fun _ _ _ _ h => h, fun q hq => ⟨q, hq.trans (Category.comp_id c), rfl⟩⟩
  totalToTarget_comp := fun _ _ =>
    Eq.symm (fixedSchemeLift_comp_incl _ (toTarget_fixed_of_auto Z hZ _ _))

/-- The image in `I_{[Y/G]}` of the object of `[Y^g/G]` attached to an object of `I_{[Y/G]}` whose
automorphism is multiplication by `g` maps to that object by the identity of its torsor. -/
def fixedSchemePullHom {g : G} (Z : AbsoluteInertia (schemeQuotientProjection.{t} B S hS G Y a))
    (hZ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (p : Z.obj.Total W),
      Z.auto.hom.map W p = Z.obj.translationMap g W p) :
    (fixedQuotientToInertia.{t} B S hS G Y a g).obj (fixedSchemePull Z hZ) ⟶ Z where
  hom := fixedSchemePullObjHom Z hZ
  comm := by
    refine Hom.ext ?_ ?_
    · change 𝟙 Z.obj.base ≫ Z.auto.hom.base = 𝟙 Z.obj.base ≫ 𝟙 Z.obj.base
      rw [auto_base]
    · funext W p
      exact hZ W p

/-- **Every object of `I_{[Y/G]}` lies locally in the image of some summand.** Its automorphism is,
locally in the fppf topology, multiplication by some `g ∈ G`, and then the object comes from
`[Y^g/G]`. -/
lemma inertia_locally_fixed (Z : AbsoluteInertia (schemeQuotientProjection.{t} B S hS G Y a)) :
    ∃ R ∈ BigFppfOver.topology B S hS ((schemeInertiaProj.{t} B S hS G Y a).obj Z),
      ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ (schemeInertiaProj.{t} B S hS G Y a).obj Z), R f →
        ∃ (g : G) (A : fixedSchemeQuotient.{t} B S hS G Y a g)
          (φ : (fixedQuotientToInertia.{t} B S hS G Y a g).obj A ⟶ Z),
          (schemeInertiaProj.{t} B S hS G Y a).IsHomLift f φ := by
  obtain ⟨R, hR, hRg⟩ := exists_covering_auto_eq_translation Z
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨g, hg⟩ := hRg f hf
  obtain ⟨Z', ψ, hψ⟩ := (inertia_isFiberedInGroupoids (B := B) (S := S) (hS := hS) (G := G)
    (X := (schemePointsFunctor B S hS).obj Y) (ρ := schemePointsAut B S hS G Y a)).exists_lift
      f Z rfl
  have hψ₁ := (RelativeInertia.isHomLift_π_comp_iff f ψ).mp hψ
  have hZ'V : Z'.obj.base = V := @IsHomLift.domain_eq _ _ _ _ _ _ _ _ _ f ψ.hom hψ₁
  have hψb : ψ.hom.base = eqToHom hZ'V ≫ f := base_of_isHomLift_tgt (A' := Z.obj) f ψ.hom hψ₁ hZ'V
  have htrans : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (p : Z'.obj.Total W),
      Z'.auto.hom.map W p = Z'.obj.translationMap g W p := by
    intro W p
    have hc : ψ.hom.map W (Z'.auto.hom.map W p) = Z.auto.hom.map W (ψ.hom.map W p) :=
      (congrFun (congrFun (congrArg Hom.map ψ.comm) W) p).symm
    have h2 : Z.auto.hom.map W (ψ.hom.map W p) = Z.obj.translationMap g W (ψ.hom.map W p) :=
      hg W.unop (p.1 ≫ eqToHom hZ'V) (ψ.hom.map W p)
        (by rw [ψ.hom.fst_map, hψb]; exact (Category.assoc _ _ _).symm)
    have h3 : Z.obj.translationMap g W (ψ.hom.map W p) =
        ψ.hom.map W (Z'.obj.translationMap g W p) :=
      (ψ.hom.map_equivariant W _ p).symm
    refine (ψ.hom.bijOn_map W p.1).injOn ?_ rfl (hc.trans (h2.trans h3))
    show (Z'.auto.hom.map W p).1 = p.1
    rw [Z'.auto.hom.fst_map, auto_base, Category.comp_id]
  refine ⟨g, fixedSchemePull Z' htrans, fixedSchemePullHom Z' htrans ≫ ψ, ?_⟩
  refine (RelativeInertia.isHomLift_π_comp_iff f _).mpr
    (isHomLift_of_base' (A' := Z.obj) f _ hZ'V ?_)
  rw [RelativeInertia.comp_hom, comp_base, hψb]
  exact Category.id_comp (eqToHom hZ'V ≫ f)

end Scheme

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : Type (max (u + 1) v)) [CommGroup G] (Y : Over S) (a : G →* Aut Y)

/-- **Stacks 0374.** Let `S` be a scheme, `G` a commutative group, `Y → S` a scheme over `S` and
`a : G →* Aut_S(Y)` an action of `G` on `Y`. Then the inertia stack of `[Y/G]` is the coproduct of
stacks `I_{[Y/G]} = ∐_{g ∈ G} [Y^g/G]`, where `Y^g = Y ×_{(1, 1), Y ×_S Y, (g, 1)} Y` is the
fixed-point scheme of `g` (`AlgebraicGeometry.fixedScheme`) with the action of `G` induced by
`a`: there is an equivalence of categories over `(Sch/S)_fppf` (a quasi-inverse over
`(Sch/S)_fppf` with unit and counit lying over identities) from the coproduct of stacks
`∐_{g ∈ G} [Y^g/G]` to `I_{[Y/G]}`, whose restriction to the `g`-th summand `[Y^g/G]` is the
canonical functor of the source, sending a torsor `P` with an equivariant map `P → Y^g` to `P`
with the composite map to `Y` and the automorphism given by multiplication by `g`. -/
@[stacks 0374 "I_{[X/G]} = ∐_{g ∈ G} [X^g/G]: an equivalence over (Sch/S)_fppf from the \
coproduct of stacks to the inertia stack, restricting on each summand to the canonical functor"]
theorem inertia_equivalence_stackCoproduct :
    ∃ H : Functor.StackCoproduct
        (fun g : G => schemeQuotientProjection.{max (u + 1) t} B S hS G (fixedScheme S G Y a g)
          (fixedSchemeAut Y a g))
        (BigFppfOver.topology B S hS) (fun _ => projection_isFiberedInGroupoids) ⥤
        AbsoluteInertia (schemeQuotientProjection.{max (u + 1) t} B S hS G Y a),
      Nonempty (Functor.IsEquivalenceOver (Functor.stackCoproductProj _ _ _)
        (schemeInertiaProj.{max (u + 1) t} B S hS G Y a) H) ∧
      ∀ g : G, Nonempty (Functor.stackCoproductι _ _ _ g ⋙ H ≅
        fixedQuotientToInertia.{max (u + 1) t} B S hS G Y a g) := by
  let q := schemeInertiaProj.{max (u + 1) t} B S hS G Y a
  let up := (ULiftHom.up : AbsoluteInertia (schemeQuotientProjection.{max (u + 1) t} B S hS G Y a) ⥤
    ULiftHom.{max (t + 1) (u + 2) v} (AbsoluteInertia
      (schemeQuotientProjection.{max (u + 1) t} B S hS G Y a)))
  have : up.Full := ⟨fun f => ⟨f.down, rfl⟩⟩
  have : up.Faithful := ⟨fun h => congrArg ULift.down h⟩
  have hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) ((schemePointsFunctor B S hS).obj Y) :=
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS Y
  obtain ⟨H, ⟨e⟩, hH⟩ := Functor.exists_isEquivalenceOver_stackCoproduct
    (p := fun g : G => schemeQuotientProjection.{max (u + 1) t} B S hS G (fixedScheme S G Y a g)
      (fixedSchemeAut Y a g))
    (fun _ => projection_isFiberedInGroupoids)
    (q := (Functor.uliftHomProj q : ULiftHom.{max (t + 1) (u + 2) v}
      (AbsoluteInertia (schemeQuotientProjection.{max (u + 1) t} B S hS G Y a)) ⥤ _))
    (Functor.isFiberedInGroupoids_uliftHomProj q inertia_isFiberedInGroupoids)
    (Functor.isStack_uliftHomProj q _ (inertia_isStack hX))
    (fun g => fixedQuotientToInertia.{max (u + 1) t} B S hS G Y a g ⋙ up) (fun _ => rfl)
    (fun g h hgh A A' m => fixedQuotientToInertia_disjoint hgh A A' m.down)
    (fun z => by
      obtain ⟨R, hR, hRz⟩ := inertia_locally_fixed (B := B) (S := S) (hS := hS) (G := G) (Y := Y)
        (a := a) z
      refine ⟨R, hR, fun V f hf => ?_⟩
      obtain ⟨g, A, φ, hφ⟩ := hRz f hf
      exact ⟨g, A, ULift.up φ, (Functor.isHomLift_uliftHomProj_iff q f _).mpr hφ⟩)
  exact ⟨H ⋙ ULiftHom.down, ⟨e.compULiftHomDown⟩,
    fun g => ⟨Functor.isoWhiskerRight (hH g).some ULiftHom.down⟩⟩

end Main

end AlgebraicGeometry

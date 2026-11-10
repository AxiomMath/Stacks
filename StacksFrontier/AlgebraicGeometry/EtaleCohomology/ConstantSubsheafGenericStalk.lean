module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# Subsheaves of a constant sheaf on an irreducible scheme

Let `X` be an irreducible scheme with generic point `η`, and let `s` be a geometric point of `X`
above `η`. If a sheaf `G` on the small étale site of `X` sits between the constant sheaves on an
inclusion `A' ⟶ A`, and if the stalk of `G` at `s` is already the stalk of the constant sheaf on
`A'`, then `G` is the constant sheaf on `A'`.

The reason is that every nonempty object of the small étale site of `X` admits a lift of `s`: the
image of an étale morphism is open, and an open set is nonempty exactly when it contains the
generic point. So a section of `G` which is locally constant with value in `A` has that value in
`A'` on every nonempty member of a covering, which makes the inclusion of the constant sheaf on
`A'` locally surjective, hence an isomorphism.

## Main results

* `AlgebraicGeometry.exists_geometricPointFiber_element_of_nonempty`: a geometric point above the
  generic point lifts to every nonempty object of the small étale site.
* `AlgebraicGeometry.constantSubsheaf_isIso_of_genericStalk`: the assertion for sheaves with
  values in an arbitrary concrete category.
* `AlgebraicGeometry.constantSetSubsheaf_eq_of_genericStalk`,
  `AlgebraicGeometry.constantAbelianSubsheaf_eq_of_genericStalk` and
  `AlgebraicGeometry.constantModuleSubsheaf_eq_of_genericStalk`: the assertions for sheaves of
  sets, of abelian groups and of modules.

## Implementation notes

An inclusion of sheaves is a monomorphism, and the equality of a subsheaf with the constant
subsheaf is the statement that the comparison morphism is an isomorphism; the hypothesis on the
generic stalk is likewise that the comparison becomes an isomorphism on the stalk. Requiring a
geometric point above a generic point of the whole space subsumes the irreducibility of `X`.

The general statement is formulated with the sheafification of the constant presheaf rather than
with `CategoryTheory.constantSheaf`, because that is the form in which the local bijectivity of
the sheafification map is available; the three statements for sheaves of sets, abelian groups and
modules are phrased with `CategoryTheory.constantSheaf`, which is the same functor.

## References

* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₂ u₂

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (η : X)
  (hη : IsGenericPoint η Set.univ) (s : GeometricPoint X) (hs : s.hom default = η)

include hη hs in
/-- A geometric point above the generic point of `X` lifts to every object of the small étale
site of `X` whose underlying scheme is nonempty: the image of an étale morphism is open, and an
open set is nonempty exactly when it contains the generic point.

See [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG). -/
public theorem exists_geometricPointFiber_element_of_nonempty (U : SmallEtale B X hX)
    (hU : Nonempty ((SmallEtale.toScheme B X hX).obj U)) :
    Nonempty ((geometricPointFiber B X hX s).obj U) := by
  have hf : Etale (B.inclusion.map U.obj.hom) := U.property
  have : Flat (B.inclusion.map U.obj.hom) := inferInstance
  have : LocallyOfFinitePresentation (B.inclusion.map U.obj.hom) := inferInstance
  obtain ⟨y⟩ := hU
  obtain ⟨z, hz⟩ := (hη.mem_open_set_iff (B.inclusion.map U.obj.hom).isOpenMap.isOpen_range).2
    ⟨(B.inclusion.map U.obj.hom).base y, Set.mem_univ _, y, rfl⟩
  have hzs : (B.inclusion.map U.obj.hom) z = s.hom default := by rwa [hs]
  obtain ⟨p, hp, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (B.inclusion.map U.obj.hom) s.hom z hzs
  exact ⟨⟨p, hp⟩⟩

section General

variable {D : Type u₂} {FD : D → D → Type*} {CD : D → Type v₂}
  [∀ A B, FunLike (FD A B) (CD A) (CD B)] [Category.{v₂} D] [ConcreteCategory.{v₂} D FD]
  [HasPullbacks D] [HasWeakSheafify (SmallEtale.topology B X hX) D]
  [(SmallEtale.topology B X hX).HasSheafCompose (forget D)]
  [(SmallEtale.topology B X hX).WEqualsLocallyBijective D]
  [UnivLE.{u, v₂}] [PreservesFilteredColimitsOfSize.{v₂, v₂} (forget D)]
  [(forget D).ReflectsIsomorphisms] [HasColimitsOfSize.{u, u} D]
  [PreservesLimitsOfShape WalkingCospan (forget D)]

include hη hs FD CD in
/-- **Stacks 09BG** for sheaves with values in a concrete category. A sheaf `G` between the
constant sheaves on `A' ⟶ A` whose stalk at a geometric point above the generic point is already
the stalk of the constant sheaf on `A'` is the constant sheaf on `A'`. -/
public theorem constantSubsheaf_isIso_of_genericStalk {A' A : D} (m : A' ⟶ A) [Mono m]
    (G : Sheaf (SmallEtale.topology B X hX) D)
    (i : (presheafToSheaf (SmallEtale.topology B X hX) D).obj
      ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj A') ⟶ G)
    (j : G ⟶ (presheafToSheaf (SmallEtale.topology B X hX) D).obj
      ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj A)) [Mono j]
    (hij : i ≫ j = (presheafToSheaf (SmallEtale.topology B X hX) D).map
      ((Functor.const (SmallEtale B X hX)ᵒᵖ).map m))
    (hstalk : IsIso ((geometricPointSitePoint B X hX s).presheafFiber.map i.hom)) :
    IsIso i := by
  have hmono : i.hom ≫ j.hom = ((presheafToSheaf (SmallEtale.topology B X hX) D).map
      ((Functor.const (SmallEtale B X hX)ᵒᵖ).map m)).hom := congrArg (·.hom) hij
  have hlocComp : Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) (i.hom ≫ j.hom) := by
    rw [hmono]
    exact (Presheaf.isLocallyInjective_presheafToSheaf_map_iff
      (J := SmallEtale.topology B X hX) ((Functor.const (SmallEtale B X hX)ᵒᵖ).map m)).2
      (Presheaf.isLocallyInjective_of_injective _ _
        (fun _ => ConcreteCategory.injective_of_mono_of_preservesPullback m))
  have hloci_inj : Presheaf.IsLocallyInjective (SmallEtale.topology B X hX) i.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective _ i.hom j.hom
  have hloci_surj : Presheaf.IsLocallySurjective (SmallEtale.topology B X hX) i.hom := by
    refine ⟨fun {V} g => (SmallEtale.topology B X hX).superset_covering ?_
      (Presheaf.imageSieve_mem (SmallEtale.topology B X hX)
        (toSheafify (SmallEtale.topology B X hX)
          ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj A)) (j.hom.app (op V) g))⟩
    rintro W f ⟨a, ha⟩
    by_cases hW : Nonempty ((SmallEtale.toScheme B X hX).obj W)
    · obtain ⟨qW⟩ := exists_geometricPointFiber_element_of_nonempty B X hX η hη s hs W hW
      have hdesc : j.hom.app (op W) (G.obj.map f.op g) =
          (toSheafify (SmallEtale.topology B X hX)
            ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj A)).app (op W) a :=
        (NatTrans.naturality_apply j.hom f.op g).trans ha.symm
      obtain ⟨b, hb⟩ := Sites.exists_preimage_of_stalk_value
        (geometricPointSitePoint B X hX s) m G i j hij hstalk W qW (G.obj.map f.op g) a hdesc
      refine ⟨(toSheafify (SmallEtale.topology B X hX)
        ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj A')).app (op W) b, ?_⟩
      have hunit := ConcreteCategory.congr_hom (NatTrans.congr_app
        (toSheafify_naturality (SmallEtale.topology B X hX)
          ((Functor.const (SmallEtale B X hX)ᵒᵖ).map m)) (op W)) b
      have hij' := ConcreteCategory.congr_hom (NatTrans.congr_app hmono (op W))
        ((toSheafify (SmallEtale.topology B X hX)
          ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj A')).app (op W) b)
      have : Mono (j.hom.app (op W)) := (NatTrans.mono_iff_mono_app j.hom).1 inferInstance (op W)
      refine ConcreteCategory.injective_of_mono_of_preservesPullback (j.hom.app (op W)) ?_
      simp only [NatTrans.comp_app, CategoryTheory.comp_apply,
        Functor.const_map_app] at hunit hij'
      rw [hij', ← hunit, hb, hdesc]
    · have hbot := Stacks.EtaleCohomology.bot_mem_topology B hX (not_nonempty_iff.mp hW)
      have key (F : Sheaf (SmallEtale.topology B X hX) D) : Unique (ToType (F.obj.obj (op W))) :=
        Types.isTerminalEquivUnique _
          (((sheafCompose (SmallEtale.topology B X hX) (forget D)).obj F).isTerminalOfBotCover
            W hbot)
      have := key G
      exact ⟨(key _).default, Subsingleton.elim _ _⟩
  exact (Sheaf.isLocallyBijective_iff_isIso i).mp ⟨hloci_inj, hloci_surj⟩

end General

include hη hs in
/-- **Stacks 09BG (1).** A subsheaf of a constant sheaf of sets on an irreducible scheme which
contains the constant subsheaf on its geometric generic stalk is that constant subsheaf. -/
@[stacks 09BG "part (1)"]
public theorem constantSetSubsheaf_eq_of_genericStalk
    [HasWeakSheafify (SmallEtale.topology B X hX) (Type (u + 1))]
    {T' T : Type (u + 1)} (m : T' ⟶ T) [Mono m]
    (G : Sheaf (SmallEtale.topology B X hX) (Type (u + 1)))
    (i : (constantSheaf (SmallEtale.topology B X hX) (Type (u + 1))).obj T' ⟶ G)
    (j : G ⟶ (constantSheaf (SmallEtale.topology B X hX) (Type (u + 1))).obj T) [Mono j]
    (hij : i ≫ j = (constantSheaf (SmallEtale.topology B X hX) (Type (u + 1))).map m)
    (hstalk : IsIso (colimMap (Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B X hX s)).op i.hom))) :
    IsIso i := by
  have : Mono (show G ⟶ (presheafToSheaf (SmallEtale.topology B X hX) (Type (u + 1))).obj
      ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj T) from j) := ‹Mono j›
  exact constantSubsheaf_isIso_of_genericStalk B X hX η hη s hs m G i j hij hstalk

include hη hs in
/-- **Stacks 09BG (2).** A subsheaf of a constant sheaf of abelian groups on an irreducible
scheme which contains the constant subsheaf on its geometric generic stalk is that constant
subsheaf. -/
@[stacks 09BG "part (2)"]
public theorem constantAbelianSubsheaf_eq_of_genericStalk
    [HasWeakSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}]
    {A' A : AddCommGrpCat.{u + 1}} (m : A' ⟶ A) [Mono m]
    (G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (i : (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj A' ⟶ G)
    (j : G ⟶ (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj A) [Mono j]
    (hij : i ≫ j = (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).map m)
    (hstalk : IsIso (colimMap (Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B X hX s)).op i.hom))) :
    IsIso i := by
  have : Mono (show G ⟶ (presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj
      ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj A) from j) := ‹Mono j›
  exact constantSubsheaf_isIso_of_genericStalk B X hX η hη s hs m G i j hij hstalk

include hη hs in
/-- **Stacks 09BG (3).** A subsheaf of a constant sheaf of modules on an irreducible scheme which
contains the constant subsheaf on its geometric generic stalk is that constant subsheaf. -/
@[stacks 09BG "part (3)"]
public theorem constantModuleSubsheaf_eq_of_genericStalk (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify (SmallEtale.topology B X hX) (ModuleCat.{u + 1} Λ)]
    {M' M : ModuleCat.{u + 1} Λ} (m : M' ⟶ M) [Mono m]
    (G : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{u + 1} Λ))
    (i : (constantSheaf (SmallEtale.topology B X hX) (ModuleCat.{u + 1} Λ)).obj M' ⟶ G)
    (j : G ⟶ (constantSheaf (SmallEtale.topology B X hX) (ModuleCat.{u + 1} Λ)).obj M) [Mono j]
    (hij : i ≫ j = (constantSheaf (SmallEtale.topology B X hX) (ModuleCat.{u + 1} Λ)).map m)
    (hstalk : IsIso (colimMap (Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B X hX s)).op i.hom))) :
    IsIso i := by
  have : Mono (show G ⟶ (presheafToSheaf (SmallEtale.topology B X hX) (ModuleCat.{u + 1} Λ)).obj
      ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj M) from j) := ‹Mono j›
  exact constantSubsheaf_isIso_of_genericStalk B X hX η hη s hs m G i j hij hstalk

end AlgebraicGeometry

end

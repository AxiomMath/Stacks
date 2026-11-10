module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
import StacksCore.Tactic.StacksAttribute

/-!
# Constructibility of the extension by zero of a constant abelian sheaf

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site. Part (2) of
Stacks 03S8 asserts that for `j : U ⟶ X` an étale morphism with `U` quasi-compact and
quasi-separated and `M` a finite abelian group, the abelian sheaf `j_!\underline{M}` is
constructible. This file proves it, from part (1) of the same tag and nothing else.

The argument is the one `Constructible/ShriekGeneratorConstructible.lean` runs for sheaves of
`Λ`-modules, with the free module sheaf functor replaced by the *copower* functor
`AddCommGrpCat.copower M`, which carries a type `E` to the direct sum `⨁_{e ∈ E} M`. It is the
left adjoint of the functor of morphisms out of `M`, and the extension by zero
`j_!\underline{M}` is the copower sheaf by `M` on `h_U^#`, by
`AlgebraicGeometry.abelianShriekConstantIsoCopower`. Since the copower of a finite group by a
finite type is finite, the constant value `E` of a trivialization of `h_U^#` on a stratum is
replaced by the finite group `⨁_{e ∈ E} M`, and the same stratification serves.

## Main results

* `AddCommGrpCat.copower` and `AddCommGrpCat.copowerAdj` — **the copower of an abelian group by a
  type**, `E ↦ ⨁_{e ∈ E} M`, and its adjunction with the functor of morphisms out of `M`.
* `CategoryTheory.Sheaf.composeAndSheafifyCopowerSheafPullbackIso`,
  `CategoryTheory.Sheaf.composeAndSheafifyCopowerOverPullbackIso` and
  `CategoryTheory.Sheaf.constantSheafComposeAndSheafifyCopowerIso` — the copower sheaf functor
  commutes with inverse image, with restriction to a localized site, and with the constant sheaf.
* `CategoryTheory.Sheaf.isFiniteLocallyConstant_composeAndSheafify_copower` — the copower sheaf by
  a finite abelian group on a finite locally constant sheaf of sets is finite locally constant.
* `CategoryTheory.Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyCopower` and
  `AlgebraicGeometry.abelianShriekConstantIsoCopower` — **the extension by zero of a constant
  abelian sheaf is a copower sheaf on a sheafified representable**, both corepresenting the
  morphisms from `M` into the sections over the étale object.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_composeAndSheafify_copower` —
  **constructibility transfers across the copower sheaf functor** at a finite abelian group.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_abelianShriekConstant` — **Stacks 03S8 part (2)**,
  unconditionally: `j_!\underline{M}` is a constructible abelian sheaf for a finite abelian group
  `M`.
* `AlgebraicGeometry.abelianShriekZModIsConstructible` — the same at the finite groups `Z/nZ`, in
  the form `AlgebraicGeometry.AbelianShriekZModIsConstructible` that the library's Stacks 09YT and
  Stacks 03SA (2) ask for.

## Implementation notes

No analogue of `CategoryTheory.Sheaf.freeSectionEquiv`'s composition with
`ModuleCat.coyonedaULiftSelfIso` is needed: the copower by `M` is adjoint to morphisms out of `M`
on the nose, so the two corepresentation statements have literally the same right-hand side and
the comparison is the preimage under `CategoryTheory.coyoneda` of their composite. The right
adjoint is `CategoryTheory.coyoneda.obj (op M)`, whose
`CategoryTheory.Functor.IsRightAdjoint` instance is
`AddCommGrpCat.coyonedaObj_isRightAdjoint`, declared a local instance so that
`CategoryTheory.GrothendieckTopology.HasSheafCompose` is available for
`CategoryTheory.Sheaf.adjunction`.

The copower functor is stated for abelian groups rather than for an arbitrary concrete category,
because `Finsupp.liftAddHom` is what furnishes the adjunction. Its coefficient universe is free,
and the corepresentation statements pin it to `max u v` for the same reason the module ones do:
the hom sets of `Sheaf J A` live in `Type (max u v_A)` while those of `A` live in `Type v_A`, so
`CategoryTheory.Sheaf.sectionEquiv` is available only when `v_A` absorbs the universe of the site.
On the small étale site of `X : B.Scheme` that universe is `u + 1`.

The terminal object of the localized site used by the constant-sheaf comparison is
`CategoryTheory.Over.mkIdTerminal`, so no terminal object of the small étale site itself is
needed.

Part (1) of Stacks 03S8 is applied in the form
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs`.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AddCommGrpCat

open Opposite

/-- **The copower of an abelian group by a type**: the functor carrying a type `E` to the direct
sum `⨁_{e ∈ E} M` of copies of `M`, realized as the finitely supported functions `E →₀ M`. At
`M = ℤ` this is the free abelian group functor; for a general `M` it is the left adjoint of the
functor of morphisms out of `M`, and it carries a finite type to a finite group as soon as `M` is
finite. -/
@[sga "4 V 7.2.0" "partial"]
public def copower (M : AddCommGrpCat.{w}) : Type w ⥤ AddCommGrpCat.{w} where
  obj E := of (E →₀ M)
  map f := ofHom (Finsupp.mapDomain.addMonoidHom f)
  map_id E := by
    ext x
    simp [Finsupp.mapDomain.addMonoidHom]
  map_comp f g := by
    ext x
    simp [Finsupp.mapDomain.addMonoidHom]

/-- The inclusion of the summand of `AddCommGrpCat.copower M` at an index `e`. -/
public def copowerMk {M : AddCommGrpCat.{w}} {E : Type w} (e : E) : M ⟶ (copower M).obj E :=
  ofHom (Finsupp.singleAddHom e)

/-- The morphism out of `AddCommGrpCat.copower M` at `E` determined by a family, indexed by `E`,
of morphisms out of `M`. -/
public def copowerDesc {M : AddCommGrpCat.{w}} {E : Type w} {A : AddCommGrpCat.{w}}
    (f : E → (M ⟶ A)) : (copower M).obj E ⟶ A :=
  ofHom (Finsupp.liftAddHom (α := E) (M := (M : Type w)) (N := (A : Type w)) fun e => (f e).hom)

/-- The morphism `AddCommGrpCat.copowerDesc f` restricts to `f e` on the summand at `e`. -/
@[simp]
public theorem copowerMk_comp_desc {M : AddCommGrpCat.{w}} {E : Type w} {A : AddCommGrpCat.{w}}
    (f : E → (M ⟶ A)) (e : E) : copowerMk e ≫ copowerDesc f = f e := by
  ext m
  change Finsupp.liftAddHom (fun e => (f e).hom) (Finsupp.single e m) = _
  exact Finsupp.liftAddHom_apply_single _ _ _

/-- The map of `AddCommGrpCat.copower M` induced by `f : E ⟶ E'` carries the summand at `e` to
the summand at `f e`. -/
@[simp]
public theorem copowerMk_comp_map {M : AddCommGrpCat.{w}} {E E' : Type w} (f : E ⟶ E') (e : E) :
    copowerMk e ≫ (copower M).map f = copowerMk (f e) := by
  ext m
  change Finsupp.mapDomain f (Finsupp.single e m) = Finsupp.single (f e) m
  exact Finsupp.mapDomain_single

/-- Two morphisms out of `AddCommGrpCat.copower M` at `E` agreeing on every summand agree. -/
public theorem copower_hom_ext {M : AddCommGrpCat.{w}} {E : Type w} {A : AddCommGrpCat.{w}}
    {f g : (copower M).obj E ⟶ A} (h : ∀ e : E, copowerMk e ≫ f = copowerMk e ≫ g) : f = g :=
  hom_ext <| Finsupp.addHom_ext' fun e => congrArg Hom.hom (h e)

/-- **Morphisms out of the copower of `M` by `E` are families of morphisms out of `M` indexed by
`E`.** -/
public def copowerHomEquiv (M : AddCommGrpCat.{w}) (E : Type w) (A : AddCommGrpCat.{w}) :
    ((copower M).obj E ⟶ A) ≃ (E ⟶ (CategoryTheory.coyoneda.obj (op M)).obj A) where
  toFun φ := ↾fun e => (copowerMk e ≫ φ : M ⟶ A)
  invFun ψ := copowerDesc fun e => (ψ e : M ⟶ A)
  left_inv _ := copower_hom_ext fun e => copowerMk_comp_desc _ e
  right_inv _ := by ext e; exact copowerMk_comp_desc _ e

/-- The inverse of `AddCommGrpCat.copowerHomEquiv` sends a family of morphisms out of `M` to the
morphism `AddCommGrpCat.copowerDesc` it determines. -/
@[simp]
public theorem copowerHomEquiv_symm_apply (M : AddCommGrpCat.{w}) (E : Type w)
    (A : AddCommGrpCat.{w}) (ψ : E ⟶ (CategoryTheory.coyoneda.obj (op M)).obj A) :
    (copowerHomEquiv M E A).symm ψ = copowerDesc (fun e => (ψ e : M ⟶ A)) := rfl

/-- **The copower by `M` is left adjoint to the functor of morphisms out of `M`.** -/
public def copowerAdj (M : AddCommGrpCat.{w}) :
    copower M ⊣ CategoryTheory.coyoneda.obj (op M) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := copowerHomEquiv M
      homEquiv_naturality_left_symm := by
        intro E E' A f g
        refine copower_hom_ext fun e => ?_
        rw [copowerHomEquiv_symm_apply, copowerHomEquiv_symm_apply, copowerMk_comp_desc,
          ← Category.assoc, copowerMk_comp_map, copowerMk_comp_desc]
        rfl }

/-- The functor of morphisms out of an abelian group is a right adjoint, the copower by that
group being its left adjoint. -/
public theorem coyonedaObj_isRightAdjoint (M : AddCommGrpCat.{w}) :
    (CategoryTheory.coyoneda.obj (op M)).IsRightAdjoint :=
  (copowerAdj M).isRightAdjoint

/-- The copower of a finite abelian group by a finite type is finite. -/
public theorem finite_copower_obj (M : AddCommGrpCat.{w}) [Finite M] (E : Type w) [Finite E] :
    Finite ((copower M).obj E) := by
  change Finite (E →₀ (M : Type w))
  exact Finite.of_equiv _ Finsupp.equivFunOnFinite.symm

end AddCommGrpCat

attribute [local instance] AddCommGrpCat.coyonedaObj_isRightAdjoint

namespace CategoryTheory.Sheaf

open Opposite AddCommGrpCat

universe u' v'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (M : AddCommGrpCat.{w})

/-- **The copower sheaf functor commutes with inverse image.** For a continuous functor `π` of
sites whose pushforward on sheaves of sets and on abelian sheaves both have left adjoints,
`M_{π^{-1}G} ≅ π^{-1}M_G`, naturally in the sheaf of sets `G`.

Both composites are left adjoint to the pushforward along `π` of the sheaf of morphisms out of
`M`, which does not depend on the order in which pushforward and that passage are performed. -/
public def composeAndSheafifyCopowerSheafPullbackIso
    [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J (Type w)]
    {D : Type u'} [Category.{v'} D] (K : GrothendieckTopology D) (π : C ⥤ D)
    [π.IsContinuous J K] [HasWeakSheafify K AddCommGrpCat.{w}] [HasWeakSheafify K (Type w)]
    [(π.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [(π.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint] :
    composeAndSheafify J (copower M) ⋙ π.sheafPullback AddCommGrpCat.{w} J K ≅
      π.sheafPullback (Type w) J K ⋙ composeAndSheafify K (copower M) :=
  Adjunction.leftAdjointUniq
    ((adjunction J (copowerAdj M)).comp (π.sheafAdjunctionContinuous AddCommGrpCat.{w} J K))
    ((π.sheafAdjunctionContinuous (Type w) J K).comp (adjunction K (copowerAdj M)))

/-- **The copower sheaf functor commutes with restriction to a localized site.** For an object
`V` of `C`, `M_{G|_V} ≅ (M_G)|_V`, naturally in the sheaf of sets `G`.

Taking the sectionwise copower commutes with restriction definitionally, both being whiskerings,
and that restriction commutes with sheafification is Mathlib's
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`. -/
public def composeAndSheafifyCopowerOverPullbackIso
    [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J (Type w)] (V : C)
    [HasWeakSheafify (J.over V) AddCommGrpCat.{w}] [HasWeakSheafify (J.over V) (Type w)]
    [∀ F : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{w}, (Over.forget V).op.HasPointwiseRightKanExtension F] :
    composeAndSheafify J (copower M) ⋙ J.overPullback AddCommGrpCat.{w} V ≅
      J.overPullback (Type w) V ⋙ composeAndSheafify (J.over V) (copower M) :=
  (Functor.isoWhiskerLeft
    (sheafToPresheaf J (Type w) ⋙
      (Functor.whiskeringRight Cᵒᵖ (Type w) AddCommGrpCat.{w}).obj (copower M))
    ((Over.forget V).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{w} (J.over V) J)).symm

/-- **The copower sheaf on a constant sheaf of sets is constant.** On a site with a terminal
object `T`, the copower sheaf by `M` on the constant sheaf of sets at `S` is the constant abelian
sheaf at the copower of `M` by `S`, naturally in `S`.

Both composites are left adjoint to the morphisms from `M` into the sections over `T`. -/
public def constantSheafComposeAndSheafifyCopowerIso
    [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J (Type w)]
    {T : C} (hT : IsTerminal T) :
    constantSheaf J (Type w) ⋙ composeAndSheafify J (copower M) ≅
      copower M ⋙ constantSheaf J AddCommGrpCat.{w} :=
  Adjunction.leftAdjointUniq
    ((constantSheafAdj J (Type w) hT).comp (adjunction J (copowerAdj M)))
    ((copowerAdj M).comp (constantSheafAdj J AddCommGrpCat.{w} hT))

/-- **The copower sheaf by a finite abelian group on a finite locally constant sheaf of sets is
finite locally constant.** A trivializing covering of the sheaf of sets serves for the copower
sheaf, with constant value the copower of `M` by the finite constant value. -/
public theorem isFiniteLocallyConstant_composeAndSheafify_copower [Finite M]
    [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J (Type w)]
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, HasWeakSheafify (J.over V) (Type w)]
    [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{w}),
      (Over.forget V).op.HasPointwiseRightKanExtension G]
    (F : Sheaf J (Type w)) (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant J F) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      ((composeAndSheafify J (copower M)).obj F) := by
  constructor
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  have : Finite E := hE
  exact ⟨(copower M).obj E, finite_copower_obj M E,
    ⟨((constantSheafComposeAndSheafifyCopowerIso (J.over (V i)) M
        Over.mkIdTerminal).app E).symm ≪≫
      (composeAndSheafify (J.over (V i)) (copower M)).mapIso e ≪≫
      ((composeAndSheafifyCopowerOverPullbackIso J M (V i)).app F).symm⟩⟩

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

open Opposite AddCommGrpCat

universe v' u'

variable {C' : Type u'} [Category.{v'} C'] {C : Type u} [Category.{v} C]

/-- **Morphisms out of the copower sheaf on a sheafified representable are sections.** A morphism
from the copower sheaf by `M` on `h_U^#` into `F` is the same thing as a morphism from `M` into
the sections of `F` over `U`: the copower adjunction transported to sheaves, followed by Yoneda's
lemma for sheaves of sets. -/
public def copowerSectionEquiv (J : GrothendieckTopology C) (M : AddCommGrpCat.{max u v})
    [HasWeakSheafify J AddCommGrpCat.{max u v}] (U : C)
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    ((composeAndSheafify J (copower M)).obj ((sheafifiedYoneda J).obj U) ⟶ F) ≃
      (coyoneda.obj (op M)).obj (F.obj.obj (op U)) :=
  ((adjunction J (copowerAdj M)).homEquiv _ F).trans (sectionEquiv J)

/-- **The copower sheaf on `h_U^#` corepresents morphisms out of `M` into the sections over `U`.**
The isomorphism of corepresented functors underlying
`CategoryTheory.Sheaf.copowerSectionEquiv`. -/
public def coyonedaComposeAndSheafifyCopowerIso (J : GrothendieckTopology C)
    (M : AddCommGrpCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}] (U : C) :
    coyoneda.obj (op ((composeAndSheafify J (copower M)).obj ((sheafifiedYoneda J).obj U))) ≅
      (sheafSections J AddCommGrpCat.{max u v}).obj (op U) ⋙ coyoneda.obj (op M) :=
  NatIso.ofComponents (fun F => Equiv.toIso (copowerSectionEquiv J M U F)) (by
    intro F G φ
    ext α
    change sectionEquiv J ((adjunction J (copowerAdj M)).homEquiv _ _ (α ≫ φ)) = _
    rw [(adjunction J (copowerAdj M)).homEquiv_naturality_right, sectionEquiv_comp]
    rfl)

/-- **The sheaf pullback of a constant abelian sheaf corepresents morphisms out of its value.**
For a continuous functor `π` out of a site with terminal object `T`, morphisms from the sheaf
pullback along `π` of the constant sheaf at `M` into `F` are morphisms from `M` into the sections
of `F` over `π.obj T`: the constant-sheaf adjunction composed with the sheaf pullback
adjunction. -/
public def coyonedaSheafPullbackConstantSheafAbelianIso (π : C' ⥤ C)
    (JC' : GrothendieckTopology C') (JC : GrothendieckTopology C) [π.IsContinuous JC' JC]
    [HasWeakSheafify JC' AddCommGrpCat.{max u v}] [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [∀ F : C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}, π.op.HasLeftKanExtension F]
    {T : C'} (hT : IsTerminal T) (M : AddCommGrpCat.{max u v}) :
    coyoneda.obj (op ((Functor.sheafPullbackConstruction.sheafPullback π
        AddCommGrpCat.{max u v} JC' JC).obj
        ((constantSheaf JC' AddCommGrpCat.{max u v}).obj M))) ≅
      (sheafSections JC AddCommGrpCat.{max u v}).obj (op (π.obj T)) ⋙ coyoneda.obj (op M) :=
  have adj := (constantSheafAdj JC' AddCommGrpCat.{max u v} hT).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous π
      AddCommGrpCat.{max u v} JC' JC)
  NatIso.ofComponents (fun F => Equiv.toIso (adj.homEquiv M F)) (by
    intro F G φ
    ext α
    change adj.homEquiv M G (α ≫ φ) = _
    rw [adj.homEquiv_naturality_right]
    rfl)

/-- **The two spellings of `j_{U!}\underline{M}_U` agree.** For a continuous functor `π` out of a
site with terminal object `T`, the sheaf pullback along `π` of the constant abelian sheaf at `M`
is the copower sheaf by `M` on the sheafified representable at `π.obj T`.

Both corepresent the morphisms from `M` into the sections over `π.obj T` — the second by
`CategoryTheory.Sheaf.coyonedaComposeAndSheafifyCopowerIso`, the first by
`CategoryTheory.Sheaf.coyonedaSheafPullbackConstantSheafAbelianIso` — and
`CategoryTheory.coyoneda` is fully faithful. -/
public def sheafPullbackConstantSheafIsoComposeAndSheafifyCopower (π : C' ⥤ C)
    (JC' : GrothendieckTopology C') (JC : GrothendieckTopology C) [π.IsContinuous JC' JC]
    (M : AddCommGrpCat.{max u v})
    [HasWeakSheafify JC' AddCommGrpCat.{max u v}] [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [∀ F : C'ᵒᵖ ⥤ AddCommGrpCat.{max u v}, π.op.HasLeftKanExtension F]
    {T : C'} (hT : IsTerminal T) :
    (Functor.sheafPullbackConstruction.sheafPullback π AddCommGrpCat.{max u v} JC' JC).obj
        ((constantSheaf JC' AddCommGrpCat.{max u v}).obj M) ≅
      (composeAndSheafify JC (copower M)).obj ((sheafifiedYoneda JC).obj (π.obj T)) :=
  (Coyoneda.fullyFaithful.preimageIso
    ((coyonedaComposeAndSheafifyCopowerIso JC M (π.obj T)).trans
      (coyonedaSheafPullbackConstantSheafAbelianIso π JC' JC hT M).symm)).unop

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

open AddCommGrpCat

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (M : AddCommGrpCat.{u + 1})

/-- **The extension by zero of a constant abelian sheaf is a copower sheaf.** For `U` an étale
object of the small étale site of `X`, the extension by zero `j_{U!}\underline{M}_U` is the
copower sheaf by `M` on the sheaf `h_U^#` of sets.

The image of the terminal object of the small étale site of `U` under composition with `U ⟶ X` is
`AlgebraicGeometry.smallEtalePostcomposeFinalIso`-isomorphic to `U`, not equal to it. -/
public def abelianShriekConstantIsoCopower (U : SmallEtale B X.obj X.property) :
    (abelianExtensionByZero B X.obj X.property U).obj
        ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
          AddCommGrpCat.{u + 1}).obj M) ≅
      (Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property) (copower M)).obj
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U) :=
  (Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyCopower
      (smallEtalePostcompose B X.obj X.property U) _ _ M
      (SmallEtale.finalIsTerminal B U.obj.left.obj U.obj.left.property)).trans
    ((Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property) (copower M)).mapIso
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).mapIso
        (smallEtalePostcomposeFinalIso B X U)))

variable
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **Constructibility transfers across the copower sheaf functor at a finite abelian group.**
The copower sheaf by a finite abelian group `M` on a constructible sheaf of sets on `X_étale` is
a constructible abelian sheaf.

The stratification furnished by the sheaf of sets serves: the copower sheaf commutes with inverse
image to a stratum, and on a stratum it carries a finite locally constant sheaf of sets to a
finite locally constant abelian sheaf. -/
public theorem isConstructibleAbelianSheaf_composeAndSheafify_copower [Finite M]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    IsConstructibleAbelianSheaf B X
      ((Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property) (copower M)).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i ↦ Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
    ((Sheaf.composeAndSheafifyCopowerSheafPullbackIso
      (SmallEtale.topology B X.obj X.property) M
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (smallEtaleBaseChange B (s.inclusion i))).app F).symm
    (hF := Sheaf.isFiniteLocallyConstant_composeAndSheafify_copower _ M _ (hs i))⟩

/-- **Stacks 03S8, part (2).** For an étale morphism `j : U ⟶ X` of quasi-compact and
quasi-separated schemes, presented as an object `U` of the small étale site of `X`, and `M` a
finite abelian group, the extension by zero `j_!\underline{M}` is a constructible abelian sheaf
on `X_étale`.

By `AlgebraicGeometry.abelianShriekConstantIsoCopower` this sheaf is the copower sheaf by `M` on
the sheaf `h_U^#` of sets, which is constructible by part (1) of the same tag; and the copower
sheaf by a finite abelian group carries a constructible sheaf of sets to a constructible abelian
sheaf. No input beyond part (1) of the tag is used. -/
@[stacks 03S8 "part (2), abelian sheaves: an extension by zero of the constant sheaf at a finite \
abelian group at a quasi-compact quasi-separated etale object is a constructible abelian sheaf"]
public theorem isConstructibleAbelianSheaf_abelianShriekConstant [Finite M]
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleAbelianSheaf B X
      ((abelianExtensionByZero B X.obj X.property U).obj
        ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
          AddCommGrpCat.{u + 1}).obj M)) := by
  intro V
  obtain ⟨s, hs⟩ := isConstructibleAbelianSheaf_composeAndSheafify_copower B X M _
    (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X U) V
  exact ⟨s, fun i ↦ Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
    (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).mapIso
        (abelianShriekConstantIsoCopower B X M U).symm) (hF := hs i)⟩

/-- **Stacks 03S8, part (2), at the finite abelian groups `Z/nZ`.** The predicate
`AlgebraicGeometry.AbelianShriekZModIsConstructible` holds: for every scheme `Y` of `B` that is
quasi-compact and quasi-separated, every quasi-compact quasi-separated étale object `U` of
`Y_étale` and every positive integer `n`, the abelian sheaf `j_{U!}(Z/nZ)` is constructible.

`ZMod n` is finite exactly because `n` is positive, so this is
`AlgebraicGeometry.isConstructibleAbelianSheaf_abelianShriekConstant` at
`M = ULift (ZMod n)`. -/
@[stacks 03S8 "part (2) at the finite groups Z/nZ, the form AbelianShriekZModIsConstructible"]
public theorem abelianShriekZModIsConstructible : AbelianShriekZModIsConstructible B := by
  intro Y U n hn hYc hYq hU
  have hc : CompactSpace Y.obj := hYc
  have hq : QuasiSeparatedSpace Y.obj := hYq
  have hUc : CompactSpace U.obj.left.obj := hU.1
  have hUq : QuasiSeparatedSpace U.obj.left.obj := hU.2
  have : NeZero n := ⟨hn.ne'⟩
  have hfin : Finite (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) :=
    inferInstanceAs (Finite (ULift.{u + 1} (ZMod n)))
  exact isConstructibleAbelianSheaf_abelianShriekConstant B Y
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) U

end AlgebraicGeometry

end

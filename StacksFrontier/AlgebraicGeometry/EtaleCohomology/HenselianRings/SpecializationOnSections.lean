module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing

/-!
# Specialization of sections on strict henselizations

A geometric point of the strict henselization of a scheme at a geometric point determines a
specialization morphism of strict henselizations, and pulling back sections along that morphism
specializes sections. The germ of a specialized section at a geometric point of the target is
the pullback of the germ of the original section.

## Main definitions

* `AlgebraicGeometry.smallEtalePullbackGlobalSections` pulls global sections of a sheaf on a
  small étale site back along a morphism of the ambient big étale site.
* `AlgebraicGeometry.smallEtalePullbackGlobalSectionsNat` assembles those maps into a natural
  transformation.
* `AlgebraicGeometry.specializationMapOnSections` is the specialization map on sections, the
  pullback of global sections along the specialization morphism of strict henselizations.
* `AlgebraicGeometry.abelianSpecializationMapOnSections` is the same map for abelian sheaves,
  as a natural transformation.

## Main results

* `AlgebraicGeometry.specializationMapOnSections_germ` identifies the geometric germ of a
  specialized section with the pullback of the germ of the original section.

## References

* [Stacks Project, Tag 0GJ4](https://stacks.math.columbia.edu/tag/0GJ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.StrictlyHenselian

universe v w u

namespace AlgebraicGeometry

/-- Base change along a morphism of the big étale site carries the final object of the small
étale site to a terminal object. -/
public def etaleBaseChangeFinalIsTerminal (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    IsTerminal ((smallEtaleBaseChange B f).obj (SmallEtale.final B Y.1 Y.property)) :=
  IsTerminal.isTerminalOfObj (SmallEtale.inclusion B X.1 X.property) _
    ((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 Y))).isTerminalObj (Over.pullback f) _)

section

variable {A : Type w} [Category.{v} A] (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [HasWeakSheafify (SmallEtale.topology B Y.1 Y.property) A]
  [HasWeakSheafify (SmallEtale.topology B X.1 X.property) A]
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).IsRightAdjoint]

/-- Pullback of global sections along a morphism `f` of the big étale site: the unit of the
pullback–pushforward adjunction read over the final object of the small étale site of the
target, restricted along the unique map from the final object of the small étale site of the
source to the base change of that final object. -/
public def smallEtalePullbackGlobalSections
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) A) :
    (Sheaf.Γ (SmallEtale.topology B Y.1 Y.property) A).obj G ⟶
      (Sheaf.Γ (SmallEtale.topology B X.1 X.property) A).obj
        (((smallEtaleBaseChange B f).sheafPullback A
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj G) :=
  let V := SmallEtale.final B Y.1 Y.property
  let U := SmallEtale.final B X.1 X.property
  let P := (smallEtaleBaseChange B f).sheafPullback A
    (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property)
  let a : U ⟶ (smallEtaleBaseChange B f).obj V :=
    (etaleBaseChangeFinalIsTerminal B f).from U
  (Sheaf.ΓNatIsoSheafSections _ _
      (SmallEtale.finalIsTerminal B Y.1 Y.property)).hom.app G ≫
    (((smallEtaleBaseChange B f).sheafAdjunctionContinuous A
      (SmallEtale.topology B Y.1 Y.property)
      (SmallEtale.topology B X.1 X.property)).unit.app G).hom.app (op V) ≫
    (P.obj G).obj.map a.op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (SmallEtale.finalIsTerminal B X.1 X.property)).inv.app (P.obj G)

/-- Pullback of global sections along `f`, as a composite of natural transformations built from
the unit of the pullback–pushforward adjunction. -/
private def smallEtalePullbackGlobalSectionsNatAux :
    Sheaf.Γ (SmallEtale.topology B Y.1 Y.property) A ⟶
      (smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property) ⋙
        Sheaf.Γ (SmallEtale.topology B X.1 X.property) A :=
  let P := (smallEtaleBaseChange B f).sheafPullback A
    (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property)
  let Q := (smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property)
  let V := SmallEtale.final B Y.1 Y.property
  let U := SmallEtale.final B X.1 X.property
  let eY := Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B Y.1 Y.property)
    A (SmallEtale.finalIsTerminal B Y.1 Y.property)
  let eX := Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B X.1 X.property)
    A (SmallEtale.finalIsTerminal B X.1 X.property)
  let secY := (sheafSections (SmallEtale.topology B Y.1 Y.property) A).obj (op V)
  let secX := (sheafSections (SmallEtale.topology B X.1 X.property) A).obj (op U)
  let a : U ⟶ (smallEtaleBaseChange B f).obj V :=
    (etaleBaseChangeFinalIsTerminal B f).from U
  let restrict : ((P ⋙ Q) ⋙ secY) ⟶ P ⋙ secX :=
    { app := fun G => (P.obj G).obj.map a.op
      naturality := fun _ _ α => ((P.map α).hom.naturality a.op).symm }
  let adj := (smallEtaleBaseChange B f).sheafAdjunctionContinuous A
    (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property)
  eY.hom ≫ (Functor.leftUnitor secY).inv ≫
    Functor.whiskerRight adj.unit secY ≫
    (Functor.associator P Q secY).hom ≫ restrict ≫
    (Functor.whiskerLeft P eX.inv)

private theorem smallEtalePullbackGlobalSectionsNatAux_app
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) A) :
    (smallEtalePullbackGlobalSectionsNatAux B f).app G =
      smallEtalePullbackGlobalSections B f G := by
  simp [smallEtalePullbackGlobalSectionsNatAux, smallEtalePullbackGlobalSections,
    Functor.comp_obj]

/-- Pullback of global sections is natural in the sheaf. -/
public theorem smallEtalePullbackGlobalSections_naturality
    {G H : Sheaf (SmallEtale.topology B Y.1 Y.property) A} (α : G ⟶ H) :
    (Sheaf.Γ (SmallEtale.topology B Y.1 Y.property) A).map α ≫
      smallEtalePullbackGlobalSections B f H =
    smallEtalePullbackGlobalSections B f G ≫
    (Sheaf.Γ (SmallEtale.topology B X.1 X.property) A).map
        (((smallEtaleBaseChange B f).sheafPullback A
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).map α) := by
  simpa only [smallEtalePullbackGlobalSectionsNatAux_app, Functor.comp_obj,
    Functor.comp_map] using (smallEtalePullbackGlobalSectionsNatAux B f).naturality α

/-- The natural transformation whose components pull global sections back along a morphism of
the big étale site. -/
public def smallEtalePullbackGlobalSectionsNat :
    Sheaf.Γ (SmallEtale.topology B Y.1 Y.property) A ⟶
      (smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property) ⋙
        Sheaf.Γ (SmallEtale.topology B X.1 X.property) A where
  app G := smallEtalePullbackGlobalSections B f G
  naturality _ _ α := smallEtalePullbackGlobalSections_naturality B f α

end

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- Specialization of a section along the canonical morphism of strict henselizations
determined by a geometric point `t` of the strict henselization at `s`: the pullback of global
sections along the specialization morphism. -/
@[stacks 0GJ4 "specialization_map_on_sections"]
public def specializationMapOnSections
    (t : GeometricPoint (strictHenselization B S hS s))
    (hT : B.Contains (strictHenselization B S hS s))
    (hU : B.Contains (strictHenselization B S hS
      (t.map (strictHenselizationToBase B S hS s))))
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) :
    let p : (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme) :=
      ⟨strictHenselizationToBase B S hS s⟩
    haveI := smallEtaleBaseChange_isContinuous B p
    let c : (⟨strictHenselization B S hS
      (t.map (strictHenselizationToBase B S hS s)), hU⟩ : B.Scheme) ⟶
      (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) :=
      ⟨specializationMorphism B S hS s t⟩
    haveI := smallEtaleBaseChange_isContinuous B c
    let G := ((smallEtaleBaseChange B p).sheafPullback (Type (u + 1))
      (SmallEtale.topology B S hS)
      (SmallEtale.topology B _ hT)).obj F
    (Sheaf.Γ (SmallEtale.topology B _ hT) (Type (u + 1))).obj G ⟶
      (Sheaf.Γ (SmallEtale.topology B _ hU) (Type (u + 1))).obj
        (((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
          (SmallEtale.topology B _ hT)
          (SmallEtale.topology B _ hU)).obj G) :=
  let p : (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme) :=
    ⟨strictHenselizationToBase B S hS s⟩
  have := smallEtaleBaseChange_isContinuous B p
  let c : (⟨strictHenselization B S hS
    (t.map (strictHenselizationToBase B S hS s)), hU⟩ : B.Scheme) ⟶
    (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) :=
    ⟨specializationMorphism B S hS s t⟩
  have := smallEtaleBaseChange_isContinuous B c
  let G := ((smallEtaleBaseChange B p).sheafPullback (Type (u + 1))
    (SmallEtale.topology B S hS)
    (SmallEtale.topology B _ hT)).obj F
  smallEtalePullbackGlobalSections B c G

/-- Specialization along the canonical morphism of strict henselizations, as a natural
transformation of functors on abelian sheaves. -/
@[stacks 0GJ4 "specialization_map_on_sections"]
public def abelianSpecializationMapOnSections
    (t : GeometricPoint (strictHenselization B S hS s))
    (hT : B.Contains (strictHenselization B S hS s))
    (hU : B.Contains (strictHenselization B S hS
      (t.map (strictHenselizationToBase B S hS s)))) :
    let p : (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme) :=
      ⟨strictHenselizationToBase B S hS s⟩
    haveI := smallEtaleBaseChange_isContinuous B p
    let c : (⟨strictHenselization B S hS
      (t.map (strictHenselizationToBase B S hS s)), hU⟩ : B.Scheme) ⟶
      (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) :=
      ⟨specializationMorphism B S hS s t⟩
    haveI := smallEtaleBaseChange_isContinuous B c
    ((smallEtaleBaseChange B p).sheafPullback Ab.{u + 1}
      (SmallEtale.topology B S hS) (SmallEtale.topology B _ hT) ⋙
      Sheaf.Γ (SmallEtale.topology B _ hT) Ab.{u + 1}) ⟶
    ((smallEtaleBaseChange B p).sheafPullback Ab.{u + 1}
      (SmallEtale.topology B S hS) (SmallEtale.topology B _ hT) ⋙
      ((smallEtaleBaseChange B c).sheafPullback Ab.{u + 1}
        (SmallEtale.topology B _ hT) (SmallEtale.topology B _ hU) ⋙
        Sheaf.Γ (SmallEtale.topology B _ hU) Ab.{u + 1})) :=
  let p : (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme) :=
    ⟨strictHenselizationToBase B S hS s⟩
  have := smallEtaleBaseChange_isContinuous B p
  let c : (⟨strictHenselization B S hS
    (t.map (strictHenselizationToBase B S hS s)), hU⟩ : B.Scheme) ⟶
    (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) :=
    ⟨specializationMorphism B S hS s t⟩
  have := smallEtaleBaseChange_isContinuous B c
  Functor.whiskerLeft
    ((smallEtaleBaseChange B p).sheafPullback Ab.{u + 1}
      (SmallEtale.topology B S hS) (SmallEtale.topology B _ hT))
    (smallEtalePullbackGlobalSectionsNat B c)

/-- The geometric germ of a specialized global section is the pullback of its germ on the first
strict henselization. -/
@[stacks 0GJ4 "specialization_map_on_sections"]
public theorem specializationMapOnSections_germ
    (t : GeometricPoint (strictHenselization B S hS s))
    (hT : B.Contains (strictHenselization B S hS s))
    (hU : B.Contains (strictHenselization B S hS
      (t.map (strictHenselizationToBase B S hS s))))
    (x : GeometricPoint (strictHenselization B S hS
      (t.map (strictHenselizationToBase B S hS s))))
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) :
    let p : (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme) :=
      ⟨strictHenselizationToBase B S hS s⟩
    haveI := smallEtaleBaseChange_isContinuous B p
    let c : (⟨strictHenselization B S hS
      (t.map (strictHenselizationToBase B S hS s)), hU⟩ : B.Scheme) ⟶
      (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) :=
      ⟨specializationMorphism B S hS s t⟩
    haveI := smallEtaleBaseChange_isContinuous B c
    let G := ((smallEtaleBaseChange B p).sheafPullback (Type (u + 1))
      (SmallEtale.topology B S hS)
      (SmallEtale.topology B _ hT)).obj F
    let H := ((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
      (SmallEtale.topology B _ hT)
      (SmallEtale.topology B _ hU)).obj G
    ∀ σ : (Sheaf.Γ (SmallEtale.topology B _ hT) (Type (u + 1))).obj G,
      ((smallEtalePullbackStalkIso B c x).hom.app G)
        ((globalSectionsToEtaleStalk B
          ↥(etaleLocalRing B S hS (t.map (strictHenselizationToBase B S hS s))) hU x H)
          (specializationMapOnSections B S hS s t hT hU F σ)) =
      (globalSectionsToEtaleStalk B ↥(etaleLocalRing B S hS s) hT
          (x.map (B.inclusion.map c)) G) σ := by
  dsimp only
  intro σ
  let p : (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) ⟶ (⟨S, hS⟩ : B.Scheme) :=
    ⟨strictHenselizationToBase B S hS s⟩
  have := smallEtaleBaseChange_isContinuous B p
  let c : (⟨strictHenselization B S hS
    (t.map (strictHenselizationToBase B S hS s)), hU⟩ : B.Scheme) ⟶
    (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) :=
    ⟨specializationMorphism B S hS s t⟩
  have := smallEtaleBaseChange_isContinuous B c
  let G := ((smallEtaleBaseChange B
      (⟨strictHenselizationToBase B S hS s⟩ :
        (⟨strictHenselization B S hS s, hT⟩ : B.Scheme) ⟶
          (⟨S, hS⟩ : B.Scheme))).sheafPullback (Type (u + 1))
    (SmallEtale.topology B S hS)
    (SmallEtale.topology B _ hT)).obj F
  let U := finalNeighborhood B
    ↥(etaleLocalRing B S hS (t.map (strictHenselizationToBase B S hS s))) hU x
  let V := finalNeighborhood B ↥(etaleLocalRing B S hS s) hT (x.map (B.inclusion.map c))
  let a := (etaleBaseChangeFinalIsTerminal B c).from U.1
  let t₀ := (Sheaf.ΓNatIsoSheafSections
    (SmallEtale.topology B _ hT) (Type (u + 1))
    (SmallEtale.finalIsTerminal B _ hT)).hom.app G σ
  let aOver := (SmallEtale.inclusion B _ hU).map a
  have h_over := Over.w aOver
  change aOver.left ≫ pullback.snd V.1.obj.hom c = U.1.obj.hom at h_over
  have hmap {X Y Z : B.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) :
      B.inclusion.map f ≫ B.inclusion.map g = B.inclusion.map h :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map e)
  have h_over_map : B.inclusion.map aOver.left ≫
      B.inclusion.map (pullback.snd V.1.obj.hom c) = B.inclusion.map U.1.obj.hom :=
    hmap h_over
  have hpull : B.inclusion.map (pullback.fst V.1.obj.hom c) ≫
      B.inclusion.map V.1.obj.hom =
        B.inclusion.map (pullback.snd V.1.obj.hom c) ≫ B.inclusion.map c :=
    hmap pullback.condition
  have ha_after : U.2.1 ≫ (SmallEtale.toScheme B _ hU).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom c) ≫ B.inclusion.map V.1.obj.hom =
        V.2.1 ≫ B.inclusion.map V.1.obj.hom := by
    change U.2.1 ≫ B.inclusion.map aOver.left ≫ B.inclusion.map (pullback.fst V.1.obj.hom c) ≫
      B.inclusion.map V.1.obj.hom = _
    erw [hpull, ← Category.assoc (B.inclusion.map aOver.left), h_over_map]
    change x.hom ≫ B.inclusion.map c = x.hom ≫ c.hom
    rfl
  have : Mono (B.inclusion.map V.1.obj.hom) :=
    inferInstanceAs (Mono (𝟙 (Spec (.of ↥(etaleLocalRing B S hS s)))))
  have ha : U.2.1 ≫ (SmallEtale.toScheme B _ hU).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom c) = V.2.1 :=
    (cancel_mono (B.inclusion.map V.1.obj.hom)).1 ha_after
  have hsection :
      (globalSectionsToEtaleStalk B
        ↥(etaleLocalRing B S hS (t.map (strictHenselizationToBase B S hS s))) hU x
        (((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
          (SmallEtale.topology B _ hT) (SmallEtale.topology B _ hU)).obj G))
        (specializationMapOnSections B S hS s t hT hU F σ) =
        colimit.ι
              ((CategoryOfElements.π (geometricPointFiber B
          (strictHenselization B S hS
            (t.map (strictHenselizationToBase B S hS s))) hU x)).op ⋙
          (((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
            (SmallEtale.topology B _ hT) (SmallEtale.topology B _ hU)).obj G).obj)
        (Opposite.op U)
        (pullbackSectionAlong B c G V.1 U.1 a t₀) := by
    let H := ((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
      (SmallEtale.topology B _ hT) (SmallEtale.topology B _ hU)).obj G
    let isoU := Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B
      (Spec (.of ↥(etaleLocalRing B S hS
        (t.map (strictHenselizationToBase B S hS s))))) hU)
      (Type (u + 1)) (SmallEtale.finalIsTerminal B
        (Spec (.of ↥(etaleLocalRing B S hS
          (t.map (strictHenselizationToBase B S hS s))))) hU)
    let z := ((((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
      (SmallEtale.topology B _ hT) (SmallEtale.topology B _ hU)).obj G).obj.map a.op)
      (((((smallEtaleBaseChange B c).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology B _ hT) (SmallEtale.topology B _ hU)).unit.app G).hom.app
        (Opposite.op V.1))
        ((Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B _ hT) (Type (u + 1)
          ) (SmallEtale.finalIsTerminal B _ hT)).hom.app G σ))
    let ι := colimit.ι
      ((CategoryOfElements.π (geometricPointFiber B
        (strictHenselization B S hS
          (t.map (strictHenselizationToBase B S hS s))) hU x)).op ⋙
        (((smallEtaleBaseChange B c).sheafPullback (Type (u + 1))
          (SmallEtale.topology B _ hT) (SmallEtale.topology B _ hU)).obj G).obj)
      (Opposite.op U)
    have hz : (ConcreteCategory.hom (isoU.hom.app H))
        ((ConcreteCategory.hom (isoU.inv.app H)) z) = z := by
      show (isoU.inv.app H ≫ isoU.hom.app H) z = z
      exact congrArg (fun g => g z) (isoU.inv_hom_id_app H)
    show ((smallEtalePullbackGlobalSections B c G) ≫
      globalSectionsToEtaleStalk B
        ↥(etaleLocalRing B S hS (t.map (strictHenselizationToBase B S hS s))) hU x H) σ = _
    dsimp only [smallEtalePullbackGlobalSections, globalSectionsToEtaleStalk]
    dsimp only [H, z, isoU, U, V, t₀, finalNeighborhood] at hz ⊢
    simp only [ConcreteCategory.comp_apply]
    exact congrArg (ConcreteCategory.hom ι) hz
  rw [hsection]
  exact smallEtalePullbackStalkIso_germ B c x G U V a ha t₀

end AlgebraicGeometry

end

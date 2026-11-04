module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Generic

/-!
# The three-factor and nine-factor composites of Tag 01MZ, on a pulled-back section

Tag 01MZ's assertion about the maps on all twists is an equation between a three-factor and a
nine-factor composite of components of the pseudofunctoriality isomorphisms of the inverse image.
This file evaluates both composites on a pulled-back section, **at the level of variables**: no
`Proj`, no twisting sheaf and no graded ring occurs below, and the comparison maps `θ` enter only
through hypotheses saying what each of them does to a pulled-back section. The concrete statement
is then obtained by instantiation, which is substitution and demands no reduction.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.threeFactor_section`: the three-factor side.
* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.nineFactor_section`: the nine-factor side.
* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistComp_section`: the two agree, given the
  identification of the two opens of the target and of the two sections over them.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.PullbackUnit
open Stacks.AlgebraicGeometry.ProjInclusionDegreeSection

namespace Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

universe u

variable {W U UP UQ Pa Pb Pc : Scheme.{u}}
  (q : W ⟶ U) (dU : U ⟶ Pa) (iU : U ⟶ Pc)
  (p : W ⟶ UP) (dP : UP ⟶ Pa) (iP : UP ⟶ Pb)
  (jj : W ⟶ UQ) (dQ : UQ ⟶ Pb) (iQ : UQ ⟶ Pc)
  {Ma : Pa.Modules} {Mb : Pb.Modules} {Mc : Pc.Modules}

/-- Pushing a comparison map through a pulled-back section that is itself pulled back. -/
private theorem pullback_map_pullbackSectionAt_of_hθ {X Y A B : Scheme.{u}} (f : X ⟶ Y)
    (d : Y ⟶ A) (i : Y ⟶ B) {M : A.Modules} {N : B.Modules}
    (θ : (Scheme.Modules.pullback d).obj M ⟶ (Scheme.Modules.pullback i).obj N)
    (T : A.Opens) (s : M.val.obj (op T)) (T' : B.Opens) (t : N.val.obj (op T'))
    (hT : i ⁻¹ᵁ T' = d ⁻¹ᵁ T)
    (hθ : θ.val.app (op (d ⁻¹ᵁ T)) (pullbackSectionOn d M T s)
      = pullbackSectionAt i N T' (d ⁻¹ᵁ T) hT t)
    {V : X.Opens} (h : f ⁻¹ᵁ (d ⁻¹ᵁ T) = V) :
    ((Scheme.Modules.pullback f).map θ).val.app (op V)
        (pullbackSectionAt f ((Scheme.Modules.pullback d).obj M) (d ⁻¹ᵁ T) V h
          (pullbackSectionAt d M T (d ⁻¹ᵁ T) rfl s))
      = pullbackSectionAt f ((Scheme.Modules.pullback i).obj N) (d ⁻¹ᵁ T) V h
          (pullbackSectionAt i N T' (d ⁻¹ᵁ T) hT t) :=
  (pullback_map_pullbackSectionAt f θ (d ⁻¹ᵁ T) h _).trans
    (congrArg (pullbackSectionAt f _ _ V h)
      ((congrArg (θ.val.app _) (pullbackSectionAt_rfl d M T rfl s)).trans hθ))

/-- **The three-factor side of Tag 01MZ's twist assertion on a pulled-back section.**

The hypothesis `hθ` says what the comparison map does to a pulled-back section: it produces the
pulled-back section, along the second leg, attached to a section `t₁` over an open `T₁` whose
inverse image is the inverse image of `T`. -/
public theorem threeFactor_section
    (θ : (Scheme.Modules.pullback dU).obj Ma ⟶ (Scheme.Modules.pullback iU).obj Mc)
    (T : Pa.Opens) (s : Ma.val.obj (op T))
    (T₁ : Pc.Opens) (t₁ : Mc.val.obj (op T₁)) (hT₁ : iU ⁻¹ᵁ T₁ = dU ⁻¹ᵁ T)
    (hθ : θ.val.app (op (dU ⁻¹ᵁ T)) (pullbackSectionOn dU Ma T s)
      = pullbackSectionAt iU Mc T₁ (dU ⁻¹ᵁ T) hT₁ t₁)
    (hV : (q ≫ dU) ⁻¹ᵁ T = q ⁻¹ᵁ (dU ⁻¹ᵁ T))
    (hV' : (q ≫ iU) ⁻¹ᵁ T₁ = q ⁻¹ᵁ (dU ⁻¹ᵁ T)) :
    ((Scheme.Modules.pullbackComp q dU).inv.app Ma ≫
          (Scheme.Modules.pullback q).map θ ≫
          (Scheme.Modules.pullbackComp q iU).hom.app Mc).val.app
        (op (q ⁻¹ᵁ (dU ⁻¹ᵁ T)))
        (pullbackSectionAt (q ≫ dU) Ma T (q ⁻¹ᵁ (dU ⁻¹ᵁ T)) hV s)
      = pullbackSectionAt (q ≫ iU) Mc T₁ (q ⁻¹ᵁ (dU ⁻¹ᵁ T)) hV' t₁ := by
  refine Eq.trans (comp_app_of _ _ _
    (pullbackComp_inv_pullbackSectionAt q dU Ma T rfl rfl hV s)) ?_
  refine Eq.trans (comp_app_of _ _ _
    (pullback_map_pullbackSectionAt_of_hθ q dU iU θ T s T₁ t₁ hT₁ hθ rfl)) ?_
  exact pullbackComp_hom_pullbackSectionAt q iU Mc T₁ hT₁ rfl hV' t₁

/-- **The nine-factor side of Tag 01MZ's twist assertion on a pulled-back section.**

The three hypotheses `hθ`, `hθφ`, `hθψ` say what each of the three comparison maps does to a
pulled-back section; every identification of two opens that the nine factors need is derived
from `hq`, `hm`, `ht` and from those three, inside the proof. -/
public theorem nineFactor_section
    (θP : (Scheme.Modules.pullback dP).obj Ma ⟶ (Scheme.Modules.pullback iP).obj Mb)
    (θQ : (Scheme.Modules.pullback dQ).obj Mb ⟶ (Scheme.Modules.pullback iQ).obj Mc)
    (hq : q ≫ dU = p ≫ dP) (hm : p ≫ iP = jj ≫ dQ) (ht : q ≫ iU = jj ≫ iQ)
    (T : Pa.Opens) (s : Ma.val.obj (op T))
    (T₂ : Pb.Opens) (t₂ : Mb.val.obj (op T₂)) (hT₂ : iP ⁻¹ᵁ T₂ = dP ⁻¹ᵁ T)
    (T₃ : Pc.Opens) (t₃ : Mc.val.obj (op T₃)) (hT₃ : iQ ⁻¹ᵁ T₃ = dQ ⁻¹ᵁ T₂)
    (hθP : θP.val.app (op (dP ⁻¹ᵁ T)) (pullbackSectionOn dP Ma T s)
      = pullbackSectionAt iP Mb T₂ (dP ⁻¹ᵁ T) hT₂ t₂)
    (hθQ : θQ.val.app (op (dQ ⁻¹ᵁ T₂)) (pullbackSectionOn dQ Mb T₂ t₂)
      = pullbackSectionAt iQ Mc T₃ (dQ ⁻¹ᵁ T₂) hT₃ t₃)
    (hV : (q ≫ dU) ⁻¹ᵁ T = q ⁻¹ᵁ (dU ⁻¹ᵁ T))
    (hfin : (jj ≫ iQ) ⁻¹ᵁ T₃ = q ⁻¹ᵁ (dU ⁻¹ᵁ T))
    (hfin' : (q ≫ iU) ⁻¹ᵁ T₃ = q ⁻¹ᵁ (dU ⁻¹ᵁ T)) :
    ((Scheme.Modules.pullbackCongr hq).hom.app Ma ≫
          (Scheme.Modules.pullbackComp p dP).inv.app Ma ≫
          (Scheme.Modules.pullback p).map θP ≫
          (Scheme.Modules.pullbackComp p iP).hom.app Mb ≫
          (Scheme.Modules.pullbackCongr hm).hom.app Mb ≫
          (Scheme.Modules.pullbackComp jj dQ).inv.app Mb ≫
          (Scheme.Modules.pullback jj).map θQ ≫
          (Scheme.Modules.pullbackComp jj iQ).hom.app Mc ≫
          (Scheme.Modules.pullbackCongr ht).inv.app Mc).val.app
        (op (q ⁻¹ᵁ (dU ⁻¹ᵁ T)))
        (pullbackSectionAt (q ≫ dU) Ma T (q ⁻¹ᵁ (dU ⁻¹ᵁ T)) hV s)
      = pullbackSectionAt (q ≫ iU) Mc T₃ (q ⁻¹ᵁ (dU ⁻¹ᵁ T)) hfin' t₃ := by
  have hVq : (p ≫ dP) ⁻¹ᵁ T = q ⁻¹ᵁ (dU ⁻¹ᵁ T) :=
    (congrArg (fun k : W ⟶ Pa => k ⁻¹ᵁ T) hq).symm.trans hV
  have hpV : p ⁻¹ᵁ (dP ⁻¹ᵁ T) = q ⁻¹ᵁ (dU ⁻¹ᵁ T) := hVq
  have hpiV : (p ≫ iP) ⁻¹ᵁ T₂ = q ⁻¹ᵁ (dU ⁻¹ᵁ T) :=
    (congrArg (fun V₀ : UP.Opens => p ⁻¹ᵁ V₀) hT₂).trans hpV
  have hjdV : (jj ≫ dQ) ⁻¹ᵁ T₂ = q ⁻¹ᵁ (dU ⁻¹ᵁ T) :=
    (congrArg (fun k : W ⟶ Pb => k ⁻¹ᵁ T₂) hm).symm.trans hpiV
  have hjV : jj ⁻¹ᵁ (dQ ⁻¹ᵁ T₂) = q ⁻¹ᵁ (dU ⁻¹ᵁ T) := hjdV
  refine Eq.trans (comp_app_of _ _ _
    (pullbackCongr_hom_pullbackSectionAt hq Ma T hV hVq s)) ?_
  refine Eq.trans (comp_app_of _ _ _
    (pullbackComp_inv_pullbackSectionAt p dP Ma T rfl hpV hVq s)) ?_
  refine Eq.trans (comp_app_of _ _ _
    (pullback_map_pullbackSectionAt_of_hθ p dP iP θP T s T₂ t₂ hT₂ hθP hpV)) ?_
  refine Eq.trans (comp_app_of _ _ _
    (pullbackComp_hom_pullbackSectionAt p iP Mb T₂ hT₂ hpV hpiV t₂)) ?_
  refine Eq.trans (comp_app_of _ _ _
    (pullbackCongr_hom_pullbackSectionAt hm Mb T₂ hpiV hjdV t₂)) ?_
  refine Eq.trans (comp_app_of _ _ _
    (pullbackComp_inv_pullbackSectionAt jj dQ Mb T₂ rfl hjV hjdV t₂)) ?_
  refine Eq.trans (comp_app_of _ _ _
    (pullback_map_pullbackSectionAt_of_hθ jj dQ iQ θQ T₂ t₂ T₃ t₃ hT₃ hθQ hjV)) ?_
  refine Eq.trans (comp_app_of _ _ _
    (pullbackComp_hom_pullbackSectionAt jj iQ Mc T₃ hT₃ hjV hfin t₃)) ?_
  exact pullbackCongr_inv_pullbackSectionAt ht Mc T₃ hfin hfin' t₃

/-- **The two composites agree on a pulled-back section**, given the identification of the two
opens of `Pc` the two sides read the value over and of the two sections over them. Every
identification of opens the nine factors need is derived here from `hq`, `hm`, `ht`, `hT₁`,
`hT₂`, `hT₃` and `hT`. -/
public theorem twistComp_section
    (θ : (Scheme.Modules.pullback dU).obj Ma ⟶ (Scheme.Modules.pullback iU).obj Mc)
    (θP : (Scheme.Modules.pullback dP).obj Ma ⟶ (Scheme.Modules.pullback iP).obj Mb)
    (θQ : (Scheme.Modules.pullback dQ).obj Mb ⟶ (Scheme.Modules.pullback iQ).obj Mc)
    (hq : q ≫ dU = p ≫ dP) (hm : p ≫ iP = jj ≫ dQ) (ht : q ≫ iU = jj ≫ iQ)
    (T : Pa.Opens) (s : Ma.val.obj (op T))
    (T₁ : Pc.Opens) (t₁ : Mc.val.obj (op T₁)) (hT₁ : iU ⁻¹ᵁ T₁ = dU ⁻¹ᵁ T)
    (T₂ : Pb.Opens) (t₂ : Mb.val.obj (op T₂)) (hT₂ : iP ⁻¹ᵁ T₂ = dP ⁻¹ᵁ T)
    (T₃ : Pc.Opens) (t₃ : Mc.val.obj (op T₃)) (hT₃ : iQ ⁻¹ᵁ T₃ = dQ ⁻¹ᵁ T₂)
    (hθ : θ.val.app (op (dU ⁻¹ᵁ T)) (pullbackSectionOn dU Ma T s)
      = pullbackSectionAt iU Mc T₁ (dU ⁻¹ᵁ T) hT₁ t₁)
    (hθP : θP.val.app (op (dP ⁻¹ᵁ T)) (pullbackSectionOn dP Ma T s)
      = pullbackSectionAt iP Mb T₂ (dP ⁻¹ᵁ T) hT₂ t₂)
    (hθQ : θQ.val.app (op (dQ ⁻¹ᵁ T₂)) (pullbackSectionOn dQ Mb T₂ t₂)
      = pullbackSectionAt iQ Mc T₃ (dQ ⁻¹ᵁ T₂) hT₃ t₃)
    (hV : (q ≫ dU) ⁻¹ᵁ T = q ⁻¹ᵁ (dU ⁻¹ᵁ T))
    (hT : T₁ = T₃) (hsec : Mc.val.map (eqToHom (congrArg op hT)) t₁ = t₃) :
    ((Scheme.Modules.pullbackComp q dU).inv.app Ma ≫
          (Scheme.Modules.pullback q).map θ ≫
          (Scheme.Modules.pullbackComp q iU).hom.app Mc).val.app
        (op (q ⁻¹ᵁ (dU ⁻¹ᵁ T)))
        (pullbackSectionAt (q ≫ dU) Ma T (q ⁻¹ᵁ (dU ⁻¹ᵁ T)) hV s)
      = ((Scheme.Modules.pullbackCongr hq).hom.app Ma ≫
          (Scheme.Modules.pullbackComp p dP).inv.app Ma ≫
          (Scheme.Modules.pullback p).map θP ≫
          (Scheme.Modules.pullbackComp p iP).hom.app Mb ≫
          (Scheme.Modules.pullbackCongr hm).hom.app Mb ≫
          (Scheme.Modules.pullbackComp jj dQ).inv.app Mb ≫
          (Scheme.Modules.pullback jj).map θQ ≫
          (Scheme.Modules.pullbackComp jj iQ).hom.app Mc ≫
          (Scheme.Modules.pullbackCongr ht).inv.app Mc).val.app
        (op (q ⁻¹ᵁ (dU ⁻¹ᵁ T)))
        (pullbackSectionAt (q ≫ dU) Ma T (q ⁻¹ᵁ (dU ⁻¹ᵁ T)) hV s) := by
  have hV' : (q ≫ iU) ⁻¹ᵁ T₁ = q ⁻¹ᵁ (dU ⁻¹ᵁ T) :=
    congrArg (fun V₀ : U.Opens => q ⁻¹ᵁ V₀) hT₁
  have hfin' : (q ≫ iU) ⁻¹ᵁ T₃ = q ⁻¹ᵁ (dU ⁻¹ᵁ T) :=
    (congrArg (fun Z₀ : Pc.Opens => (q ≫ iU) ⁻¹ᵁ Z₀) hT).symm.trans hV'
  have hfin : (jj ≫ iQ) ⁻¹ᵁ T₃ = q ⁻¹ᵁ (dU ⁻¹ᵁ T) :=
    (congrArg (fun k : W ⟶ Pc => k ⁻¹ᵁ T₃) ht).symm.trans hfin'
  refine Eq.trans
    (threeFactor_section q dU iU θ T s T₁ t₁ hT₁ hθ hV hV') ?_
  refine Eq.trans
    (pullbackSectionAt_congr (q ≫ iU) Mc hT hV' hfin' t₁ t₃ hsec) ?_
  exact (nineFactor_section q dU iU p dP iP jj dQ iQ θP θQ hq hm ht T s T₂ t₂ hT₂
    T₃ t₃ hT₃ hθP hθQ hV hfin hfin').symm

end Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

end
